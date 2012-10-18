build:
	ghc-7.6.1 -O -o agsyHOL --make -rtsopts Main

clean:
	rm *.hi *.o *~ agsyHOL

