AGDA=agda

PRELUDE?=../agda-prelude/src

.PHONY : html

all : html

html : 
	$(AGDA) --html -i. -i$(PRELUDE) README.agda -v0
