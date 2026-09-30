.POSIX:
.PHONY: todo all lint clean distclean

all:
	agda src/Index.agda

todo:
	find . -name "*.agda" -type f -exec grep -q "TODO" {} ";" -print -exec grep -nA 6 "TODO" {} ";"

lint:
	find . -name "*.agda" -type f -exec sed -i "s/[ 	]*$$//" {} ";"

clean:
	find . -name "*.agdai" -type f -delete
	find . -name "*.agda.vim" -type f -delete

distclean: clean
	rm -rf _build
