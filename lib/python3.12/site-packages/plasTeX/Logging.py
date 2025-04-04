import textwrap
from logging import CRITICAL, DEBUG, INFO, Formatter
from logging import Logger as _Logger
from logging import StreamHandler as _StreamHandler
from logging import addLevelName, setLoggerClass, FileHandler, Filter
from plasTeX.Config import defaultConfig

MAX_WIDTH = 75
LOG_FORMAT = '[%(name)s] %(levelname)s: %(message)s'
STATUS_FORMAT = '%(message)s'
ROOT_LOG_FORMAT = '%(levelname)s: %(message)s'

DEBUG1 = DEBUG - 1
DEBUG2 = DEBUG - 2
DEBUG3 = DEBUG - 3
DEBUG4 = DEBUG - 4
DEBUG5 = DEBUG - 5

addLevelName(DEBUG1, 'DEBUG-1')
addLevelName(DEBUG2, 'DEBUG-2')
addLevelName(DEBUG3, 'DEBUG-3')
addLevelName(DEBUG4, 'DEBUG-4')
addLevelName(DEBUG5, 'DEBUG-5')

class Logger(_Logger):

    def __init__(self, name='', *args, **kwargs):
        _Logger.__init__(self, name, *args, **kwargs)
        self.propagate = 0
        level = locals().get(defaultConfig()['logging']['logging'].get(name))
        if not name:
            handler = StreamHandler()
            handler.setFormatter(StreamFormatter(ROOT_LOG_FORMAT))
        elif name in ['status', '(status)']:
            handler = StatusHandler()
            handler.setFormatter(StreamFormatter(STATUS_FORMAT))
            level = INFO
        else:
            handler = StreamHandler()
            handler.setFormatter(StreamFormatter(LOG_FORMAT))
        self.addHandler(handler)
        if level is not None:
            self.setLevel(level)

    def debug1(self, *args, **kwargs):
        return self.log(DEBUG1, *args, **kwargs)

    def debug2(self, *args, **kwargs):
        return self.log(DEBUG2, *args, **kwargs)

    def debug3(self, *args, **kwargs):
        return self.log(DEBUG3, *args, **kwargs)

    def debug4(self, *args, **kwargs):
        return self.log(DEBUG4, *args, **kwargs)

    def debug5(self, *args, **kwargs):
        return self.log(DEBUG5, *args, **kwargs)

    def dot(self):
        return self.info('.')


class StreamFormatter(Formatter):

    def format(self, record):
        """ Format the specified record as text. """
        record.message = record.getMessage()
        if self._fmt.count("%(asctime)"):
            record.asctime = self.formatTime(record, self.datefmt)
        s = self._fmt % record.__dict__
        if record.exc_info:
            if s[-1] != "\n":
                s = s + "\n"
            s = s + self.formatException(record.exc_info)
        return '\n   '.join(textwrap.wrap(s, MAX_WIDTH))


class StreamHandler(_StreamHandler):

    currentpos = 0
    lastwrite = None

    def emit(self, record):
        """ Emit a record.  """
        try:
            msg = self.format(record)

            try:
                self.checkLastWrite()
                self.stream.write("%s\n" % msg)
            except (UnicodeDecodeError, UnicodeEncodeError):
                self.checkLastWrite()
                self.stream.write("%s\n" % msg.encode("UTF-8"))

            StreamHandler.currentpos = 0
            StreamHandler.lastwrite = StreamHandler
            self.flush()
        except:
            self.handleError(record)

    def checkLastWrite(self):
        if StreamHandler.lastwrite == StatusHandler:
            self.stream.write('\n')
            StreamHandler.currentpos = 0

    def checkPos(self, length):
        pos = StreamHandler.currentpos
        if pos and pos + length > MAX_WIDTH:
            self.stream.write('\n')
            StreamHandler.currentpos = 0
        StreamHandler.currentpos += length


class StatusHandler(StreamHandler):
    """ StreamHandler with no newlines after each emit """

    def emit(self, record):
        """ Emit a record.  """
        try:
            msg = self.format(record)

            try:
                self.checkPos(len(msg))
                self.stream.write(msg)
            except (UnicodeDecodeError, UnicodeEncodeError):
                msg = msg.encode("UTF-8")
                self.checkPos(len(msg))
                self.stream.write(msg)

            StreamHandler.lastwrite = StatusHandler
            self.flush()
        except:
            self.handleError(record)


setLoggerClass(Logger)

root = Logger()

_loggers = {None:root}

def getLogger(name=None):
    """
    Return a logger with the specified name, creating it if necessary.

    If no name is specified, return the root logger.
    """
    if name:
        logger = Logger.manager.getLogger(name)
        _loggers[name] = logger
        return logger
    else:
        return root

def disableLogging():
    """ Disable all logging """
    for logger in list(_loggers.values()):
        logger.setLevel(CRITICAL)

def fileLogging(fname):
    """
    Remove all StreamHandlers;
    Add a single FileHandler (filename given as arg);
    Add a filter to omit dots.

    """
    def dotfilter(record):
        if not isinstance(record.msg, str) or record.msg.strip() != '.':
            return True
    logfilter = Filter()
    logfilter.filter = dotfilter

    fhandler = FileHandler(fname, 'w')
    for logger in list(_loggers.values()):
        for handler in logger.handlers:
            logger.removeHandler(handler)
        logger.addHandler(fhandler)
        logger.addFilter(logfilter)

def updateLogLevels(levels):
    """
    Update logging levels from dictionary
    whose keys are logger names and values are levels
    (both are strings).
    Non-existent loggers are created.
    Loggers whose names are not keys of the input dictionary are unaffected.
    """
    for name, lvl in levels.items():
        getLogger(None if name == 'root' else name).setLevel(lvl)
