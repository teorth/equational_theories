#!/usr/bin/env python3

import os, sys
import importlib
import traceback, pdb
import plasTeX
from plasTeX import __version__
from argparse import ArgumentParser
from plasTeX.Logging import getLogger
from plasTeX.Compile import run
from plasTeX.Config import defaultConfig

log = getLogger()

def collect_renderer_config(config):
    plastex_dir = os.path.dirname(os.path.realpath(plasTeX.__file__))
    renderers_dir = os.path.join(plastex_dir, 'Renderers')
    renderers = next(os.walk(renderers_dir))[1]
    for renderer in renderers:
        try:
            conf = importlib.import_module('plasTeX.Renderers.'+renderer+'.Config')
        except ImportError as msg:
            continue

        conf.addConfig(config)

def main(argv):
    """ Main program routine """
    print('plasTeX version %s' % __version__)

    config = defaultConfig()
    collect_renderer_config(config)

    parser = ArgumentParser("plasTeX")

    group = parser.add_argument_group("External Configuration Files")
    group.add_argument("--config", "-c", dest="config", help="Config files to load. Non-existent files are silently ignored", action="append")

    config.registerArgparse(parser)

    parser.add_argument("file", help="File to process")

    data = parser.parse_args(argv)
    data = vars(data)
    if data["config"] is not None:
        config.read(data["config"])

    config.updateFromDict(data)

    filename = data["file"]

    run(filename, config)

def info(type, value, tb):
   if hasattr(sys, 'ps1') or not sys.stderr.isatty():
      # we are in interactive mode or we don't have a tty-like
      # device, so we call the default hook
      sys.__excepthook__(type, value, tb)
   else:
      # we are NOT in interactive mode, print the exception...
      traceback.print_exception(type, value, tb)
      print()
      # ...then start the debugger in post-mortem mode.
      pdb.pm()

#sys.excepthook = info

#sys.setrecursionlimit(10000)

def plastex():
    try:
        main(sys.argv[1:])
    except KeyboardInterrupt:
        pass
