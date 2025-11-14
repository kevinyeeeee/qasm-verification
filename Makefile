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
	cabal build tcqasm && python3 generate-data.py benchmarks/pldi/ benchmarks/pldi-qft-increasing/ benchmarks/pldi-cuccaro-increasing/ benchmarks/pldi-in-place-mult/

regenerate-data:
	rm -rf generated-data/* && cabal build tcqasm && python3 generate-data.py benchmarks/pldi/ benchmarks/pldi-qft-increasing/ benchmarks/pldi-cuccaro-increasing/ benchmarks/pldi-in-place-mult/

clean-data:
	rm -rf generated-data/*