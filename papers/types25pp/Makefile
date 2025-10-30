# all sources needed to build the paper
SOURCES = $(wildcard *.tex *.cls *.sty *.bib)
# sources for the arxiv version
ARXIV_SOURCES = $(filter-out $(wildcard *types*),$(wildcard *.tex *.cls *.sty *.bib *.bbl))
# sources for the camera-ready version
TYPESPP_SOURCES = types25pp-sort-final.tex $(filter-out $(wildcard *arxiv*)$(wildcard *types*),$(wildcard *.tex *.cls *.sty *.bib *.bbl))
# targets to build: full paper, and the stripped submission
TARGETS = arxiv-sort.tex types25pp-sort-strip.tex types25pp-sort.pdf types25pp-sort-submission.pdf
# latexmk setup
DEPS_DIR = .deps
ENGINE = -pdf
LATEXMK = latexmk -recorder -use-make $(ENGINE)
# helper programs
PDFTK = pdftk

all: $(TARGETS)

types25pp-sort-strip.tex: types25pp-sort.tex
	cp -f $< $@

types25pp-sort.pdf: $(SOURCES)
	$(LATEXMK) types25pp-sort.tex

arxiv-sort.tex: types25pp-sort.tex
	cp -f $< $@

arxiv-sort.pdf: ENGINE = -pdf
arxiv-sort.pdf: $(SOURCES)
	$(LATEXMK) arxiv-sort.tex

types25pp-sort-strip.pdf: $(SOURCES)
	$(LATEXMK) types25pp-sort-strip.tex

# Builds both full and stripped versions, counts the pages in the
# stripped version, then cuts that many pages from the full version
types25pp-sort-submission.pdf: types25pp-sort-strip.pdf types25pp-sort.pdf
	$(eval NUMPAGES=$(shell $(PDFTK) types25pp-sort-strip.pdf dump_data | grep NumberOfPages | grep -o -E '[[:digit:]]+'))
	@echo Number of pages in submission is: $(NUMPAGES)
	$(PDFTK) types25pp-sort.pdf cat 1-$(NUMPAGES) output types25pp-sort-submission.pdf

cont: continuous
continuous: LATEXMK += -f -interaction=nonstopmode -pvc
continuous: $(SOURCES)
	$(LATEXMK) types25pp-sort.tex

fast-continuous: LATEXMK += -f -interaction=nonstopmode -pvc
fast-continuous: $(SOURCES)
	$(LATEXMK) types25pp-sort-strip.tex

arxiv.tar.gz:
	tar achvf arxiv.tar.gz $(ARXIV_SOURCES)

types25pp-sort-final.pdf: $(SOURCES)
	$(LATEXMK) types25pp-sort-final.tex
	mv types25pp-sort-final.pdf types25pp-sort-final-full.pdf
	$(PDFTK) types25pp-sort-final-full.pdf cat 1-28 output types25pp-sort-final.pdf
	rm types25pp-sort-final-full.pdf

types25pp-sort-final.zip: $(SOURCES)
	zip types25pp-sort-final.zip $(CPP_SOURCES)

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
