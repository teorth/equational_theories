import http.server
import logging
import os
import platform
import re
import shutil
import socketserver
import subprocess
import sys
import tomlkit
from tomlkit.toml_file import TOMLFile
from tomlkit import TOMLDocument
from collections import deque
from pathlib import Path
from typing import Any, Dict, List, Optional, NoReturn
from textwrap import dedent
from abc import ABC, abstractmethod

import rich_click as click
from git.exc import GitCommandError, InvalidGitRepositoryError
from git.repo import Repo
from jinja2 import Environment, FileSystemLoader
from rich.console import Console
from rich.prompt import Confirm, IntPrompt, Prompt
from rich.theme import Theme

log = logging.getLogger("Mathlib tools")
log.setLevel(logging.INFO)
if (log.hasHandlers()):
    log.handlers.clear()
log.addHandler(logging.StreamHandler())

# Click aliases from Stephen Rauch at
# https://stackoverflow.com/questions/46641928


class CustomMultiCommand(click.RichGroup):
    def command(self, *args, **kwargs):  # type: ignore
        """Behaves the same as `click.Group.command()` except if passed
        a list of names, all after the first will be aliases for the first.
        """
        def decorator(f):
            if args and isinstance(args[0], list):
                _args = [args[0][0]] + list(args[1:])
                for alias in args[0][1:]:
                    cmd = super(CustomMultiCommand, self).command(
                        alias, *args[1:], **kwargs)(f)
                    cmd.short_help = "Alias for '{}'".format(_args[0])
                    cmd.hidden = True
            else:
                _args = args
            cmd = super(CustomMultiCommand, self).command(
                *_args, **kwargs)(f)
            return cmd

        return decorator

    """Allows the user to shorten commands to a (unique) prefix."""

    def get_command(self, ctx, cmd_name):
        rv = click.Group.get_command(self, ctx, cmd_name)
        if rv is not None:
            return rv
        matches = [x for x in self.list_commands(ctx)
                   if x.startswith(cmd_name)]
        if not matches:
            return None
        elif len(matches) == 1:
            return click.Group.get_command(self, ctx, matches[0])
        ctx.fail('Too many matches: %s' % ', '.join(sorted(matches)))


class Lakefile(ABC):
    def __init__(self, path: Path):
        self.path = path

    @abstractmethod
    def parse_libs(self) -> List[str]:
        """
        Extract list of libraries from the lakefile. If the lakefile has a
        default target, it will be the first element of the returned list.
        """
        pass

    @abstractmethod
    def add_checkdecls(self) -> None:
        """Update the lakefile to add a requirement for checkdecls"""
        pass

    @abstractmethod
    def add_docgen(self) -> None:
        """Update the lakefile to add a requirement for docgen"""
        pass

class LakefileLean(Lakefile):
    def __init__(self, lakefile_lean: Path):
        super().__init__(lakefile_lean)

    def parse_libs(self) -> List[str]:
        """see `super.parse_libs`"""
        libs: List[str] = []
        lib_re = re.compile(r"\s*lean_lib\s*([^ ]*)\b")
        default_re = re.compile(r"@\[default_target\]")
        found_default = False
        with self.path.open("r", encoding="utf8") as lf:
            for line in lf:
                m = lib_re.match(line)
                if m:
                    lib_name = m.group(1).strip("«» ")
                    if found_default:
                        libs.insert(0,lib_name)
                    else:
                        libs.append(lib_name)
                found_default = bool(default_re.match(line))
        return libs

    def add_checkdecls(self) -> None:
        """see `super.add_checkdecls`"""
        with self.path.open("a") as lf:
            lf.write('\nrequire checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"')

    def add_docgen(self) -> None:
        """see `super.add_docgen"""
        with self.path.open("a", encoding="utf8") as lf:
            lf.write(dedent('''

                meta if get_config? env = some "dev" then
                require «doc-gen4» from git
                  "https://github.com/leanprover/doc-gen4" @ "main"'''))

class LakefileToml(Lakefile):
    def __init__(self, lakefile_toml: Path):
        self._file = TOMLFile(lakefile_toml)
        self._toml: TOMLDocument = self._file.read()
        super().__init__(lakefile_toml)

    def parse_libs(self) -> List[str]:
        """see `super.parse_libs`"""
        defaults = self._toml.get('defaultTargets', [])
        libs: List[str] = []
        for lib in self._toml.get("lean_lib", []):
            if lib['name'] in defaults:
                libs.insert(0, lib['name'])
            else:
                libs.append(lib['name'])

        return libs

    def add_checkdecls(self) -> None:
        """see `super.add_checkdecls`"""
        self._add_require("checkdecls", "https://github.com/PatrickMassot/checkdecls.git")

    def add_docgen(self) -> None:
        """see `super.add_docgen`"""
        self._add_require("«doc-gen4»", "https://github.com/leanprover/doc-gen4", rev="main")

    def _add_require(self, name:str, git:str, rev:Optional[str] = None) -> None:
        """Add a [[require]] to self._toml and dump it"""
        require = tomlkit.aot()
        item = {'name':name,'git':git}
        if rev:
            item['rev'] = rev
        require.append(tomlkit.item(item))

        self._toml.append("require", require)
        self._file.write(self._toml)

debug = False


def handle_exception(exc, msg):
    if debug:
        raise exc
    else:
        log.error(msg)
        sys.exit(-1)


custom_theme = Theme({
    "info": "italic",
    "warning": "yellow",
    "error": "bold red",
    "title": "bold",
    "prompt.default": "dim",
    "prompt.choices": "default"
})

console = Console(theme=custom_theme)


def ask(*args, **kwargs) -> str:
    kwargs.update({'console': console})
    return Prompt.ask(*args, **kwargs)


def confirm(*args, **kwargs) -> bool:
    kwargs.update({'console': console})
    return Confirm.ask(*args, **kwargs)


def askInt(*args, **kwargs) -> int:
    kwargs.update({'console': console})
    return IntPrompt.ask(*args, **kwargs)


def warning(msg: str) -> None:
    console.print(f"[warning]Warning:[/] {msg}")


def error(msg: str) -> NoReturn:
    console.print(f"[error]Error:[/] {msg}")
    sys.exit(1)


@click.group(cls=CustomMultiCommand, context_settings={'help_option_names': ['-h', '--help']})
@click.option('--debug', 'python_debug', default=False, is_flag=True,
              help='Display python tracebacks in case of error.')
@click.version_option()
def cli(python_debug: bool) -> None:
    """Command line client to manage Lean blueprints.
    Use leanblueprint COMMAND --help to get more help on any specific command."""
    global debug
    debug = python_debug


# locate repo

repo: Optional[Repo] = None
try:
    repo = Repo(".", search_parent_directories=True)
except InvalidGitRepositoryError:
    error("Could not find a Lean project. Please run this command from inside your project folder.")

assert repo is not None

# locate lakefile

lakefile_lean_path = Path(repo.working_dir)/"lakefile.lean"
lakefile_toml_path = Path(repo.working_dir)/"lakefile.toml"

lakefile: Optional[Lakefile] = None

if lakefile_lean_path.exists() and lakefile_toml_path.exists():
    warning("Both lakefile.lean and lakefile.toml exist; using lakefile.lean")
    lakefile = LakefileLean(lakefile_lean_path)
elif lakefile_lean_path.exists():
    lakefile = LakefileLean(lakefile_lean_path)
elif lakefile_toml_path.exists():
    lakefile = LakefileToml(lakefile_toml_path)
else:
    error(f"Could not find lakefile.lean or lakefile.toml in {repo.working_dir}")

# blueprint root directory

blueprint_root = Path(repo.working_dir)/"blueprint"

@cli.command()
def new() -> None:
    """
    Create a new Lean blueprint in the given repository.
    """
    assert lakefile is not None
    loader = FileSystemLoader(Path(__file__).parent/"templates")
    env = Environment(loader=loader, variable_start_string='{|', variable_end_string='|}',
                      comment_start_string='{--', comment_end_string='--}')

    console.print("\nWelcome to Lean blueprint\n", style="title")
    can_try_ci = True

    if repo is None:
        error("Could not find a Lean project. Please run this command from inside your project folder.")

    if repo.is_dirty():
        error("The repository contains uncommitted changes. Please clean it up before creating a blueprint.")

    # Will now try to guess the author name
    try:
        name = repo.git.config("user.name")
    except GitCommandError:
        try:
            # Name of the author of the first commit.
            name = deque(repo.iter_commits(), 1)[0].author.name
        except (IndexError, ValueError):
            # This will happen if there is no commit in the repo.
            name = "Anonymous"


    libs = lakefile.parse_libs()
    if not libs:
        warning(
            "Could not find Lean library names in lakefile. Will not propose to setup continuous integration.")
        can_try_ci = False

    manifest_path = Path(repo.working_dir)/"lake-manifest.json"

    # Will now try to guess the GitHub url
    github = ""
    githubIO = ""
    doc_home = ""
    githubUserName = ""
    githubRepoName = ""
    try:
        url = repo.remote().url
    except ValueError:
        url = None
    if url:
        patterns = [r"https://github.com/(.*)/(.*)\.git",
                    r"https://github.com/(.*)/(.*)",
                    r"git@github.com:(.*)/(.*)\.git",
                    r"git@github.com:(.*)/(.*)"]
        m = next(m for m in map(lambda p: re.match(p, url), patterns) if m is not None)
        if m:
            githubUserName = m.group(1)
            githubRepoName = m.group(2)
        if githubUserName:
            github = f"https://github.com/{githubUserName}/{githubRepoName}"
            githubIO = f"https://{githubUserName}.github.io/{githubRepoName}"
            doc_home = f"https://{githubUserName}.github.io/{githubRepoName}/docs"
        else:
            warning(
                "Could not guess GitHub information. Will not propose to setup continuous integration.")
            can_try_ci = False

    out_dir = Path(repo.working_dir)/"blueprint"
    if out_dir.exists():
        error("There is already a blueprint folder. Aborting blueprint creation.")

    console.print("We will now ask some questions to configure your blueprint. All answers can be changed later by editing either the plastex.cfg file or the tex files.")
    config: Dict[str, Any] = dict()

    if 'master' in repo.heads:
        config['master_branch'] = "master"
    elif 'main' in repo.heads:
        config['master_branch'] = "main"
    else:
        config['master_branch'] = ask("\nName of your main Git branch")

    config['github_username'] = githubUserName
    config['github_projectname'] = githubRepoName

    console.print("\nGeneral information about the project", style="title")
    config['title'] = ask("Project title", default="My formalization project")
    if len(libs) > 1:
        config['lib_name'] = ask(
            "Lean library name", choices=libs, default=libs[0])
    else:
        config['lib_name'] = libs[0]
    config['author'] = ask(
        "Author ([info]use \\and to separate authors if needed[/])", default=name)

    config['github'] = ask("URL of GitHub repository", default=github)
    config['home'] = ask("URL of project website", default=githubIO)
    config['dochome'] = ask(
        "URL of project API documentation", default=doc_home)

    console.print("\nLaTeX settings for the pdf version", style="title")
    config['documentclass'] = ask("LaTeX document class", default="report")
    config['paper'] = ask("LaTeX paper", default="a4paper")

    console.print("\nLaTeX settings for the web version", style="title")
    config['showmore'] = confirm(
        "Show buttons allowing to show or hide all proofs", default=True)
    config['toc_depth'] = askInt("Table of contents depth", default=3)
    config['split_level'] = askInt(
        "Split file level [info](0 means each chapter gets a file, 1 means the same for sections etc.[/])", default=0)
    config['localtoc_level'] = askInt(
        "Per html file local table of contents depth [info](0 means there will be no local table of contents)[/]", default=0)

    console.print("\nConfiguration completed", style="title")

    if not confirm("Proceed with blueprint creation?"):
        error("Aborting blueprint creation per user request.")

    out_dir.mkdir()
    (out_dir/"src").mkdir()
    for tpl_name in env.list_templates():
        if tpl_name.endswith("blueprint.yml"):
            continue
        tpl = env.get_template(tpl_name)
        path = out_dir/"src"/tpl_name
        path.parent.mkdir(parents=True, exist_ok=True)
        tpl.stream(config).dump(str(path))

    if platform.system() == 'Windows':
        console.print(
            "\nBlueprint source successfully created in the blueprint folder.\n")
    else:
        console.print(
            "\nBlueprint source successfully created in the blueprint folder :tada:\n")

    console.print("\nLake configuration updating", style="title")
    console.print("The next two questions are crucial for the blueprint infrastructure. Please use the default answer unless you are really sure you already did the necessary work.")

    if confirm("Modify lakefile and lake-manifest to allow checking declarations exist?",
               default=True):
        lakefile.add_checkdecls()
        console.print("Ok, lakefile is edited. Will now get the declaration check library. Note this may be long if you just created the project and did not yet get Mathlib.")
        subprocess.run("lake update checkdecls",
                       cwd=str(blueprint_root.parent), check=False, shell=True)

    if confirm("Modify lakefile and lake-manifest to allow building the documentation?",
               default=True):
        lakefile.add_docgen()
        console.print("Ok, lakefile is edited. Will now get the doc-gen library.")
        subprocess.run("lake -R -Kenv=dev update doc-gen4",
                       cwd=str(blueprint_root.parent), check=False, shell=True)
        
    home_page_created = False

    if confirm("Do you want to create a home page for the project, "
               "with links to the blueprint, the API documentation and the "
               "repository?"):
        jekyll_loader = FileSystemLoader(Path(__file__).parent/"jekyll_templates")
        jekyll_env = Environment(loader=jekyll_loader, variable_start_string='{|', variable_end_string='|}',
                        comment_start_string='{--', comment_end_string='--}',
                        block_start_string='{%|', block_end_string='|%}')
        jekyll_out_dir = Path(repo.working_dir)/"home_page"
        if jekyll_out_dir.exists():
            error("There is already a home_page folder. Aborting.")
        else:
            home_page_created = True  
            author = config['author'].replace("\\and", "and") 
            config['web_title'] = ask("Home page title?", default=config["title"])
            config['web_subtitle'] = ask("Home page subtitle?", default=f"by {author}") 
            config['jekyll_theme'] = ask("Jekyll theme? (see https://github.com/pages-themes)", default="pages-themes/cayman@v0.2.0") 
            jekyll_out_dir.mkdir()
            for tpl_name in jekyll_env.list_templates():
                print(f"Handling {tpl_name}")
                tpl = jekyll_env.get_template(tpl_name)
                path = jekyll_out_dir/tpl_name
                path.parent.mkdir(parents=True, exist_ok=True)
                tpl.stream(config).dump(str(path))
            console.print("Ok, the home page template is created in `home_page`.")
            console.print("The main file you want to edit there is `index.md`.")

    workflow_files: List[Path] = []
    if can_try_ci and confirm("Configure continuous integration to compile blueprint?",
                              default=True):
        tpl = env.get_template("blueprint.yml")
        path = Path(repo.working_dir)/".github"/"workflows"
        path.mkdir(parents=True, exist_ok=True)
        tpl.stream(config).dump(str(path/"blueprint.yml"))
        console.print(
            f"GitHub workflow file created at {path/'blueprint.yml'}")
        workflow_files.append(path/'blueprint.yml')

    files_to_add = [out_dir, lakefile.path, manifest_path] + workflow_files

    if home_page_created:
        files_to_add.append(jekyll_out_dir)

    if not confirm("\nCommit to git repository?"):
        console.print("You are all set! Don’t forget to commit whenever you feel ready.")
        sys.exit(0)

    msg = ask("Commit message", default="Setup blueprint")
    repo.index.add(files_to_add)
    repo.index.commit(msg)
    console.print(
        "Git commit created. Don't forget to push when you are ready.")
    if platform.system() == 'Windows':
        console.print("\nYou are all set!\n")
    else:
        console.print("\nYou are all set :tada:\n")

def mk_pdf() -> None:
    (blueprint_root/"print").mkdir(exist_ok=True)
    subprocess.run("latexmk -output-directory=../print", cwd=str(
        blueprint_root/"src"), check=True, shell=True)
    bbl_path = blueprint_root/"print"/"print.bbl"
    if bbl_path.exists():
        shutil.copy(bbl_path, blueprint_root/"src"/"web.bbl")
    
@cli.command()
def pdf() -> None:
    """
    Compile the pdf version of the blueprint using latexmk.
    """
    mk_pdf()


def mk_web() -> None:
    (blueprint_root/"web").mkdir(exist_ok=True)
    subprocess.run("plastex -c plastex.cfg web.tex",
                   cwd=str(blueprint_root/"src"), check=True, shell=True)
@cli.command()
def web() -> None:
    """
    Compile the html version of the blueprint using plasTeX.
    """
    mk_web()

def do_checkdecls() -> None:
    subprocess.run("lake exe checkdecls blueprint/lean_decls",
                   cwd=str(blueprint_root.parent), check=True, shell=True)

@cli.command()
def checkdecls() -> None:
    """
    Check that each declaration mentioned in the blueprint exists in Lean.
    Requires to build the project and the blueprint first.
    """
    do_checkdecls()


@cli.command()
def all() -> None:
    """
    Compile both the pdf and html versions of the blueprint and check declarations.
    """
    mk_pdf()
    mk_web()
    subprocess.run("lake build",
                   cwd=str(blueprint_root.parent), check=True, shell=True)
    do_checkdecls()



@cli.command()
def serve() -> None:
    """
    Launch a web server to see the (already compiled) blueprint.

    This is useful is order to see the dependency graph in particular.
    """
    cwd = os.getcwd()
    os.chdir(blueprint_root/'web')
    Handler = http.server.SimpleHTTPRequestHandler
    httpd = None
    for port in range(8000, 8010):
        try:
            httpd = socketserver.TCPServer(("", port), Handler)
            break
        except OSError:
            pass
    if httpd is None:
        print("Could not find an available port.")
        sys.exit(1)
    try:
        (ip, port) = httpd.server_address
        ip = ip or 'localhost'
        print(f'Serving http://{ip}:{port}/ \nPress Ctrl-c to interrupt.')
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    httpd.server_close()
    os.chdir(cwd)


def safe_cli():
    try:
        cli()  # pylint: disable=no-value-for-parameter
    except Exception as err:
        handle_exception(err, str(err))


if __name__ == "__main__":
    # This allows `python3 -m leanblueprint.client`.
    # This is useful for when python is on the path but its installed scripts are not
    safe_cli()
