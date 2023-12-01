Redex formalism of the Checked C paper (and extensions)

#Download and Install Racket

Please find racket in the following link: https://docs.racket-lang.org/pollen/Installation.html

Download racket and install it.

Open a .rkt file and then you can see the Checked C model and test cases. The specific files are listed below.


#Redex Model

The file post.rkt contains the basic Checked C model.

The file nt-array.rkt contains the CoreChkC model listed in the paper.

The file nt-array-test.rkt contains test cases for the CoreChkC model.

The random testing generator is in the files: compiled-checknt.rkt, to-checkc.rkt and run-shell.rkt.


To generate tests in the redex model, you can use the function (loop n) to generate n number of expressions, and (loop2 1) to generate an indefinite number of expressions.
To generate expressions and convert them to clang you must set the PATH-TO-RACKET variable to your local path to racket, and the PATH-TO-CHECKEDC variable to your local path to the clang compiler.  Use (run) to generate an indefinite number of expressions, or (test-res n) to generate n expressions and test them against the clang compiler.

