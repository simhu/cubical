OPT=2
GHC=ghc
#GHC=cabal exec ghc --

all:
	$(GHC) --make -O$(OPT) -o cubical Main.hs
debug:
	$(GHC) --make -Ddebugmode -O$(OPT) -o cubical Main.hs
profile:
	$(GHC) --make -O$(OPT) -prof -rtsopts -auto-all -caf-all -fprof-auto -o cubical Main.hs

bnfc:
	bnfc --haskell -d Exp.cf
	happy -gca Exp/Par.y
	alex -g Exp/Lex.x
	$(GHC) --make -O$(OPT) Exp/Test.hs -o Exp/Test
clean:
	rm -f *.log *.aux *.hi *.o cubical
	cd Exp && rm -f ParExp.y LexExp.x LexhExp.hs \
                        ParExp.hs PrintExp.hs AbsExp.hs *.o *.hi
tests:

	$(GHC) --make -O2 -main-is Tests.main Tests.hs

