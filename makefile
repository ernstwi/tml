all: test

test:
	mi main.mc

brief:
	mi main.mc | grep -e '--'

.PHONY: test brief
