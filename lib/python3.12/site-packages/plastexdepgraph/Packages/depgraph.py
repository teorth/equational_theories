"""
Package Dependency graphs

Options:
* title: the title of the dependency graph.
        The default value is Dependencies.
* dep_by: optional level for dependency graph generation, for instance chapter
        or part.
        The default value is to generate one graph for the whole document
* thms: optional list of theorem types to include into the report,
        separated by +.
        The default value is: definition+lemma+proposition+theorem+corollary
* nonreducedgraph: keep all edges in the dependency, even transitively
        redundant ones.
* tpl: template file for dependency graph, relative to the current
  directory

This package will also consider optional information contained in the document
userdata dictionary. Such information could be added by other packages who
want to influence the dependency graph.

* document.userdata['dep_graph']['shapes'] can be a dictionary whose keys are node
  kinds as strings and whose values are strings descripting graphviz shapes
  (see https://graphviz.org/doc/info/shapes.html).
  By default, everything uses an ellipse except definition which uses a box.

* document.userdata['dep_graph']['colorizer'] can be a function taking as input
  a plasTeX node and outputting a CSS color for the boundary of graph nodes.

* document.userdata['dep_graph']['fillcolorizer'] can be a function taking as
  input a plasTeX node and outputting a CSS color for the interior of graph
  nodes.

* document.userdata['dep_graph']['stylerizer'] can be a function taking as input
  a plasTeX node and outputting a graphviz style
  (see https://graphviz.org/docs/attr-types/style/).

* document.userdata['dep_graph']['legend'] can be a list whose entries are pairs
  made of a visual description and an explanation.
  The default value is:
  [('Boxes', 'definitions'), ('Ellipses', 'theorems and lemmas')]
  Additional entries can also refer to colors.

* document.userdata['dep_graph']['extra_modal_links'] can be a list of Jinja2
  templates used to render extra links at the bottom of the modal appearing
  when clicking on graph nodes.
  The default value is an empty list.
"""
import string
from pathlib import Path
from typing import Optional

from jinja2 import Template
from pygraphviz import AGraph

from plasTeX import Command, Environment
from plasTeX.PackageResource import (
        PackageTemplateDir, PackageJs, PackageCss, PackagePreCleanupCB)

from plasTeX.Logging import getLogger
log = getLogger()

PKG_DIR = Path(__file__).parent
STATIC_DIR = Path(__file__).parent.parent/'static'
DEFAULT_TYPES = 'definition+lemma+proposition+theorem+corollary'


def item_kind(node) -> str:
    """Return the kind of declaration corresponding to node"""
    if hasattr(node, 'thmName'):
        return node.thmName
    if node.parentNode:
        return item_kind(node.parentNode)
    return ''


class DepGraph():
    """
    A TeX declarations dependency graph, built using the `\\uses and `\\proves` commands.
    """
    def __init__(self):
        self.nodes = set()
        self.edges = set()
        self.proof_edges = set()
        self.document = None
        self._ancestors = dict()
        self._predecessors = dict()

    def predecessors(self, node):
        """
        Return direct predecessors of the given node, as a set.
        This is meant to be called only after all nodes have been added since the result is cached.
        """
        if node in self._predecessors:
            return self._predecessors[node]
        else:
            return self._predecessors.setdefault(node, {e[0] for e in self.edges.union(self.proof_edges) if e[1] == node})

    def ancestors(self, node):
        """
        Return ancestors of the given node, as a set.
        This is meant to be called only after all nodes have been added since the result is cached.
        """
        if not node in self.nodes:
            return set()
        else:
            if node in self._ancestors:
                return self._ancestors[node]
            else:
                pred = self.predecessors(node)
                return self._ancestors.setdefault(node,
                                pred.union(*map(self.ancestors, pred)))


    def to_dot(self, shapes: dict) -> AGraph:
        """Convert to pygraphviz AGraph"""
        graph = AGraph(directed=True, bgcolor='transparent')
        graph.node_attr['penwidth'] = 1.8
        graph.edge_attr.update(arrowhead='vee')
        for node in self.nodes:
            color = self.document.userdata['dep_graph'].get('colorizer', lambda x: '')(node)
            fillcolor = self.document.userdata['dep_graph'].get('fillcolorizer', lambda x: '')(node)

            if fillcolor:
                style = self.document.userdata['dep_graph'].get('stylerizer', lambda x: 'filled')(node)

                graph.add_node(node.id,
                               label=node.id.split(':')[-1],
                               shape=shapes.get(item_kind(node), 'ellipse'),
                               style=style,
                               color=color,
                               fillcolor=fillcolor)
            else:
                style = self.document.userdata['dep_graph'].get('stylerizer', lambda x: '')(node)
                graph.add_node(node.id,
                               label=node.id.split(':')[-1],
                               shape=shapes.get(item_kind(node), 'ellipse'),
                               style=style,
                               color=color)
        for s, t in self.edges:
            if s in self.nodes and t in self.nodes:
                graph.add_edge(s.id, t.id, style='dashed')
        for s, t in self.proof_edges:
            if s in self.nodes and t in self.nodes:
                graph.add_edge(s.id, t.id)
        return graph

class bpcolor(Command):
    r"""\bpcolor{key}{color}{description}"""
    args = 'key:str color:str descr:str'

    def invoke(self, tex):
        Command.invoke(self, tex)
        colors = self.ownerDocument.userdata['dep_graph']['colors']
        key = self.attributes['key']
        color = self.attributes['color']
        descr = self.attributes['descr']
        if key not in colors:
            valid = ', '.join(colors.keys())
            log.error(f'Invalid dependency graph color key: {key}. Valid keys are {valid}.')
            return []
        colors[key] = (color, descr)
        return []

class uses(Command):
    r"""\uses{labels list}"""
    args = 'labels:list:nox'

    def digest(self, tokens):
        Command.digest(self, tokens)
        node = self.parentNode
        doc = self.ownerDocument
        def update_used():
            labels_dict = doc.context.labels
            used = [labels_dict[label]
                    for label in self.attributes['labels'] if label in labels_dict]
            for label in self.attributes['labels']:
                if label not in labels_dict:
                    log.error("Label '" + label + "' could not be resolved")
            node.setUserData('uses', used)

        doc.addPostParseCallbacks(10, update_used)

class alsoIn(Command):
    r"""\uses{labels list}"""
    args = 'labels:list:nox'

    def digest(self, tokens):
        Command.digest(self, tokens)
        node = self.parentNode
        doc = self.ownerDocument
        def update_incls():
            """
            Updates the doc.userdata['graph_includes'] dict.
            Each key in this dict is a section object,
            and the corresponding value is a list of nodes
            to also include in the dep graph of that section.
            """
            labels_dict = doc.context.labels
            alsoin = [labels_dict[label]
                      for label in self.attributes['labels']
                      if label in labels_dict]
            incls = doc.userdata.setdefault('graph_includes', dict())
            for decl in alsoin:
                incls.setdefault(decl, []).append(node)

        doc.addPostParseCallbacks(10, update_incls)

class proves(Command):
    r"""\proves{label}"""
    args = 'label:str'

    def digest(self, tokens):
        Command.digest(self, tokens)
        node = self.parentNode
        doc = self.ownerDocument
        def update_proved() -> None:
            labels_dict = doc.context.labels
            proved = labels_dict.get(self.attributes['label'])
            if proved:
                node.setUserData('proves', proved)
                proved.userdata['proved_by'] = node
        doc.addPostParseCallbacks(10, update_proved)


def find_proved_thm(proof) -> Optional[Environment]:
    """From a proof node, try to find the statement."""
    node = proof.parentNode
    while node.previousSibling:
        childNodes = node.previousSibling.childNodes
        if childNodes and childNodes[0].nodeName == 'thmenv':
            return childNodes[0]
        node = node.previousSibling
    return None

LINK_TPL = Template("""
    <a class="icon proof" href="{{ obj.url }}">#</a>
""")

PROVED_BY_TPL = Template("""
    {% if obj.userdata.proved_by %}
    <a class="icon proof" href="{{ obj.userdata.proved_by.url }}">{{ icon('cogs') }}</a>
    {% endif %}
""")

USES_TPL = Template("""
    {% if obj.userdata.uses %}
    <button class="modal">{{ icon('mindmap') }}</button>
    {% call modal(context.terms.get('Uses', 'Uses')) %}
        <ul class="uses">
          {% for used in obj.userdata.uses %}
          <li><a href="{{ used.url }}">{{ used.caption }} {{ used.ref }}</a></li>
          {% endfor %}
        </ul>
    {% endcall %}
    {% endif %}
""")

def ProcessOptions(options, document):
    """This is called when the package is loaded."""

    document.rendererdata.setdefault('html5', dict())
    document.userdata['dep_graph'] = dict()

    templatedir = PackageTemplateDir(path=PKG_DIR/'renderer_templates')
    document.addPackageResource(templatedir)

    jobname = document.userdata['jobname']
    outdir = document.config['files']['directory']
    outdir = string.Template(outdir).substitute({'jobname': jobname})

    def update_proofs() -> None:
        for proof in document.getElementsByTagName('proof'):
            proved = proof.userdata.setdefault('proves', find_proved_thm(proof))
            if proved:
                proved.userdata['proved_by'] = proof
    document.addPostParseCallbacks(100, update_proofs)

    ## Dep graph
    title = options.get('title', 'Dependencies')

    def makegraph(section, title:str) -> None:
        nodes = []
        for thm_type in document.userdata['dep_graph']['thm_types']:
            nodes += section.getElementsByTagName(thm_type)
        # Add nodes that used \alsoIn
        incls = document.userdata.get('graph_includes', dict())
        nodes.extend(incls.get(section, []))

        graph = DepGraph()
        graph.document = document
        graph.nodes = set(nodes)
        for node in nodes:
            used = node.userdata.get('uses', [])
            for thm in used:
                graph.edges.add((thm, node))
            proof = node.userdata.get('proved_by')
            if proof:
                used = proof.userdata.get('uses', [])
                for thm in used:
                    graph.proof_edges.add((thm, node))

        graphs = document.userdata['dep_graph'].setdefault('graphs', dict())
        graphs[section] = graph

    def makegraphs() -> None:
        dep_by = options.get('dep_by', '')
        if dep_by:
            for section in document.getElementsByTagName(dep_by):
                graph_target = 'dep_graph_' + section.counter + '_' + section.ref.textContent + '.html'
                document.rendererdata['html5']['extra_toc_items'].append({
                    'text': section.counter.capitalize() + ' ' + section.ref.textContent + ' graph',
                    'url': graph_target})
                makegraph(section, title)
        else:
            document.rendererdata['html5']['extra_toc_items'].append({'text': 'Dependency graph','url': 'dep_graph_document.html'})
            makegraph(document, title)

    document.rendererdata['html5'].setdefault('extra_toc_items', [])
    document.addPostParseCallbacks(110, makegraphs)

    default_tpl_path = PKG_DIR.parent/'templates'/'dep_graph.html'
    graph_tpl_path = Path(options.get('tpl', default_tpl_path))
    try:
        graph_tpl = Template(graph_tpl_path.read_text())
    except IOError:
        log.warning('DepGraph template read error, using default template')
        graph_tpl = Template(default_tpl_path.read_text())

    reduce_graph = not options.get('nonreducedgraph', False)

    def make_graph_html(document):
        files = []
        for sec, graph in document.userdata['dep_graph']['graphs'].items():
            if sec == document:
                name = 'document'
            else:
                name = sec.counter + '_' + sec.ref.textContent
            graph_target = 'dep_graph_' + name + '.html'
            files.append(graph_target)
            dot = graph.to_dot(document.userdata['dep_graph'].get('shapes', {'definition': 'box'}))
            if reduce_graph:
                dot = dot.tred()
            graph_tpl.stream(graph=graph,
                             dot=dot.to_string(),
                             context=document.context,
                             title=title,
                             legend=document.userdata['dep_graph']['legend'],
                             extra_modal_links=document.userdata['dep_graph'].get('extra_modal_links_tpl', []),
                             document=document,
                             config=document.config).dump(graph_target)
        return files

    cb = PackagePreCleanupCB(data=make_graph_html)
    css = PackageCss(path=STATIC_DIR/'dep_graph.css', copy_only=True)
    js = [PackageJs(path=STATIC_DIR/name, copy_only=True)
          for name in ['d3.min.js', 'hpcc.min.js', 'd3-graphviz.js',
                       'expatlib.wasm', 'graphvizlib.wasm']]

    document.addPackageResource([cb, css] + js)


    thm_types = [thm.strip()
                 for thm in options.get('thms', DEFAULT_TYPES).split('+')]
    document.userdata['dep_graph']['thm_types'] = thm_types

    document.userdata['thm_header_extras_tpl'] = []
    document.userdata['thm_header_hidden_extras_tpl'] = [LINK_TPL,
                                                         PROVED_BY_TPL,
                                                         USES_TPL]

    document.userdata['dep_graph']['legend'] = [('Boxes', 'definitions'), ('Ellipses', 'theorems and lemmas')]
    document.userdata['dep_graph']['extra_modal_links'] = []

