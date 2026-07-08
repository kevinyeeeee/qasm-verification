all:
	cabal build
	cp dist/build/feynopt/feynopt ./feynopt
	cp dist/build/feynver/feynver ./feynver


.PHONY: feynopt
feynopt:
	cabal build exe:feynopt
	cp dist/build/feynopt/feynopt ./feynopt

.PHONY: feynver
feynver:
	cabal build exe:feynver
	cp dist/build/feynver/feynver ./feynver

generate-data:
	cabal build tcqasm && python3 generate-data.py benchmarks/popl/

regenerate-data:
	rm -rf generated-data/* && cabal build tcqasm && python3 generate-data.py benchmarks/popl/

clean-data:
	rm -rf generated-data/*