# clean:
# 	rm **/*.log **/*.aux **/*.synctex.gz **/*.fdb_latexmk **/*.fls **/*.bbl **/*.bcf **/*.blg **/*.run.xml **/*.out
clean:
	rm -f *.log */*.log */*/*.log *.aux */*.aux */*/*.aux *.synctex.gz */*.synctex.gz */*/*.synctex.gz *.fdb_latexmk */*.fdb_latexmk */*/*.fdb_latexmk *.fls */*.fls */*/*.fls *.bbl */*.bbl */*/*.bbl *.bcf */*.bcf */*/*.bcf *.blg */*.blg */*/*.blg *.run.xml */*.run.xml */*/*.run.xml *.out */*.out */*/*.out *.tlc */*.tlc */*/*.tlc *.dvi */*.dvi */*/*.dvi
	rm -rf */*/states
commit: 
	bash autocommit.sh