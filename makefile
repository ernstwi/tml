all: test

test:
	mi main.mc -- test/*.in

quiet:
	mi main.mc -- --quiet test/*.in

utest:
	mi test main.mc

.PHONY: test quiet utest
.SILENT: test quiet utest
