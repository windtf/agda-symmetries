# all sources needed to build the paper
SOURCES = $(wildcard *.tex *.cls *.sty *.bib)
# sources for the arxiv version
ARXIV_SOURCES = $(filter-out $(wildcard *types*),$(wildcard *.tex *.cls *.sty *.bib *.bbl) cc-by.pdf lipics-logo-bw.pdf orcid.pdf)
# sources for the camera-ready version
TYPESPP_SOURCES = types25pp-sort.tex $(filter-out $(wildcard *arxiv*)$(wildcard *types*),$(wildcard *.tex *.cls *.sty *.bib *.bbl))
# targets to build: full paper, and the stripped submission
TARGETS = types25pp-sort.pdf arxiv-sort.pdf
# latexmk setup
DEPS_DIR = .deps
ENGINE = -pdf
LATEXMK = latexmk -recorder -use-make $(ENGINE)
# helper programs
PDFTK = pdftk

all: $(TARGETS)

types25pp-sort.pdf: $(SOURCES)
	$(LATEXMK) types25pp-sort.tex

arxiv-sort.tex: types25pp-sort.tex
	cp -f $< $@ || true

arxiv-sort.pdf: $(SOURCES)
	$(LATEXMK) arxiv-sort.tex

cont: continuous
continuous: LATEXMK += -f -interaction=nonstopmode -pvc
continuous: $(SOURCES)
	$(LATEXMK) types25pp-sort.tex

arxiv.tar.gz:
	tar achvf arxiv.tar.gz $(ARXIV_SOURCES)

types25pp-sort.zip: $(SOURCES)
	zip types25pp-sort.zip $(TYPESPP_SOURCES)

deploy: all
	rsync -avchzP types25pp-sort.pdf vikraman@internal.vikraman.org:_site/files/

fast-deploy: LATEXMK += -f -interaction=nonstopmode
fast-deploy: deploy

cont-deploy: continuous-deploy
continuous-deploy: $(SOURCES)
	watchman-make -p '**/*.tex' '**/*.bib' '**/*.cls' '**/*.sty' -t fast-deploy

clean:
	latexmk -c

distclean: clean
	latexmk -C
	rm -rf *.axp *.xcp *.bbl *.blg *.aux *.xml *.cut *.pdf

cache-clean:
	rm -rf `biber --cache`

.PHONY: clean distclean cache-clean cont continuous fast-continuous deploy fast-deploy cont-deploy continuous-deploy
