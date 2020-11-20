all: test

test:
	mi src/main.mc -- tsa test/tsa/*.in
	mi src/main.mc -- tsa+sync test/tsa-sync/*.in

quiet:
	mi src/main.mc -- --quiet tsa test/tsa/*.in
	mi src/main.mc -- --quiet tsa+sync test/tsa-sync/*.in

write:
	mi src/main.mc -- --write tsa test/tsa/*.in
	mi src/main.mc -- --write tsa+sync test/tsa-sync/*.in

utest:
	mi test src/*.mc

.PHONY: test quiet write utest
