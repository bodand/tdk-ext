.POSIX:
.PHONY:

all:
	agda src/Index.agda

clean:
	find . -name "*.agdai" -type f -delete

distclean: clean
	rm -rf _build
