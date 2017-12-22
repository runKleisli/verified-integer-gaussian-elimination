IDRIS     := idris
PKG       := zzgauss

build:
	$(IDRIS) --build ${PKG}.ipkg

clean:
	$(IDRIS) --clean ${PKG}.ipkg

install:
	$(IDRIS) --install ${PKG}.ipkg

rebuild: clean build

doc:
	$(IDRIS) --mkdoc ${PKG}.ipkg

doc_clean:
	rm -rf ${PKG}_doc

.PHONY: build clean install rebuild doc doc_clean
