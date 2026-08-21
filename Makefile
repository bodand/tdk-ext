.POSIX:
.PHONY: all lint clean distclean

all:
	agda src/Index.agda

lint:
	find . -name "*.agda" -type f -exec sed -i "s/[ 	]*$$//" {} ";"

clean:
	find . -name "*.agdai" -type f -delete
	find . -name "*.agda.vim" -type f -delete

distclean: clean
	rm -rf _build
