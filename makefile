all: test

test:
	mi main.mc

brief:
	mi main.mc | grep -e '--'

utest:
	TMPFILE=$$(mktemp XXX) || exit 1; \
	printf "include \"quiet.mc\"\n$$(cat main.mc)" > $$TMPFILE; \
	mi test $$TMPFILE; \
	rm $$TMPFILE

.PHONY: test brief utest
.SILENT: test brief utest
