all: test

test:
	mi src/main.mc -- test/*.in

quiet:
	mi src/main.mc -- --quiet test/*.in

utest:
	mi test src/*.mc

.PHONY: test quiet utest
.SILENT: test quiet utest
