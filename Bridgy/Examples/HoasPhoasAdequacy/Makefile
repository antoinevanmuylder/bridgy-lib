
.PHONY : agdas
agdas:
	echo "typechecking..."
	find . -type f -iname '*.agda' -exec agda {} \;

.PHONY : clean
clean:
	find . -type f -name '*.agdai' -delete
