all: 
	ghc --make -o cubical Main.hs
bnfc:
	bnfc --haskell -d Exp.cf
	happy -gca Exp/Par.y
	alex -g Exp/Lex.x
	ghc --make Exp/Test.hs -o Exp/Test
clean:
	rm -f *.log *.aux *.hi *.o cubical
	cd Exp && rm -f ParExp.y LexExp.x LexhExp.hs \
                        ParExp.hs PrintExp.hs AbsExp.hs *.o *.hi
