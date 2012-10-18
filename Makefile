build:
	ghc -O -o agsyHOL --make -rtsopts Main

clean:
	rm *.hi *.o *~ agsyHOL

