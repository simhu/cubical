all:
	ghc --make -O2 -o cubigle Main.hs
clean:
	rm -f *.hi *.o
