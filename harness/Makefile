CFLAGS ?= -O2 -Wall -Wextra

loader: loader.c
	$(CC) $(CFLAGS) -o $@ $<

diff: loader manifest.tsv
	sudo python3 diff.py manifest.tsv

clean:
	rm -f loader

.PHONY: diff clean
