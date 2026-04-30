
.PHONY : agdas
agdas:
	echo "typechecking..."
	find . -type f -iname '*.agda' -exec agda --trace-imports=0 {} \;

.PHONY : clean
clean:
	find . -type f -name '*.agdai' -delete
