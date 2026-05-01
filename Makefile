AGDA_FILES = $(shell find Bridgy -name "*.agda" \
    -not -path "Bridgy/Old/*" \
    -not -path "Bridgy/Experimental/*" \
    -not -path "Bridgy/Test/*")

.PHONY: all
all: $(AGDA_FILES:.agda=.agdai)

%.agdai: %.agda
	agda $<

.PHONY: clean
clean:
	find . -name "*.agdai" -delete
