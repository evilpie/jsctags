PREFIX=/usr/local
INSTALL=install
NODE=node

BIN_SRC=$(addprefix bin/,jsctags.js)
LIB_SRC=$(addprefix lib/jsctags/,getopt.js log.js paperboy.js traits.js \
	underscore.js)
LIB_CTAGS_SRC=$(addprefix lib/jsctags/ctags/,index.js interp.js nativefn.js \
	reader.js writer.js)
LIB_NARCISSUS_SRC=$(addprefix lib/jsctags/narcissus/,index.js jscfa.js \
    jsdefs.js jslex.js jsparse.js)

install:
	$(INSTALL) -d $(PREFIX)/bin
	$(INSTALL) $(BIN_SRC) $(BIN_SRC:%.js=$(PREFIX)/%)
	$(INSTALL) -d $(PREFIX)/lib/jsctags
	$(INSTALL) $(LIB_SRC) $(PREFIX)/lib/jsctags
	$(INSTALL) -d $(PREFIX)/lib/jsctags/ctags
	$(INSTALL) $(LIB_CTAGS_SRC) $(PREFIX)/lib/jsctags/ctags
	$(INSTALL) -d $(PREFIX)/lib/jsctags/narcissus
	$(INSTALL) $(LIB_NARCISSUS_SRC) $(PREFIX)/lib/jsctags/narcissus

uninstall:
	rm -rf $(BIN_SRC:%.js=$(PREFIX)/%) $(PREFIX)/lib/jsctags

serve:
	$(NODE) serve.js

tags:
	$(NODE) bin/jsctags.js -Llib/jsctags js lib/jsctags

.PHONY:	all install uninstall serve tags

