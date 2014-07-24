docs := logic_project.pdf Makefile README
coqfiles := PropLogic.v Intro.v hw1_prob1.v hw1_prob2.v
contents := $(docs) $(coqfiles)

prop : 
	coqc PropLogic.v

intro : PropLogic.vo
	coqc Intro.v

hw1 : PropLogic.vo
	coqc hw1_prob1.v

package :
	tar -czvf logic_project.tgz $(contents)
