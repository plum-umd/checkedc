TARGETS = main


LATEX   = pdflatex -shell-escape
BIBTEX  = bibtex

all:  $(MSC_RENDERED) $(TARGETS) debug

$(TARGETS):
	$(LATEX) $@
	-$(BIBTEX) $@ > $(BIBTEX)_out.log
	$(LATEX) $@
	$(LATEX) $@
	$(LATEX) $@

debug:
	-grep Warning *.log

clean:
	rm -f images/*.aux images/*.log *.aux *.bbl *.blg *.log *.dvi *.bak *~ $(TARGETS:%=%.pdf)
