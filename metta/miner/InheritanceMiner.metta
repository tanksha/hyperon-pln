; ### Algorithm Sketch

; Given a collection of data trees T, a minimum support ms and an
; initial collection of patterns Candidate (containing at least the identity
; pattern, the pattern mining algorithm works as follows

; 1. Select a pattern P from C
; 2. Extract the valuation set of P over T, called V
; 3. Determine the shallow abstractions of V, called A
; 4. Specialize P by composing it with elements in A
; 5. Add the resulting specializations with enough support in C,
;    discard the others
; 6. Repeat till termination

; Load sample data
; !(import! &self example.metta)
!(import! &self canonical_toy-example-mining.metta)

;; lib
!(import! &self ../common/Num.metta)

;; Parameters
(= (minsup) 1)
(= (maxiter) 10)
(= (highsurp) 0.5)

;; Helper function
(= (tupleLength $tuple) (if (== $tuple ()) 0 (+ 1 (tupleLength (cdr-atom $tuple)))))

;; Ignore non-strongly connected components
;; e.g (, (Inheritance $Xvar "Concept man") (Inheritance "Concept Abe" $Yvar))
;; is not strongly connected
(= (getvar (, (Inheritance $a $b) (Inheritance $Candidate $d)) $Xvar $Yvar)
(if (and (== $a $c) (== $b $d)) None 
    (if (and (== $a $Xvar) (== $Candidate $Xvar)) $Xvar 
        (if (and (== $b $Yvar) (== $d $Yvar)) $Yvar None))))

(= (getvar (, (Inheritance $a $b) (Inheritance $Candidate $d) (Inheritance $e $f)) $Xvar $Yvar)
(if (and (== $a $c) (and (== $b $d) (and (== $Candidate $e) (== $d $f)))) None
    (if (and (== $a $c) (== $b $d)) 
        (getvar (, (Inheritance $Candidate $d) (Inheritance $e $f)) $Xvar $Yvar)
        (if (or (and (== $a $e) (== $b $f)) (and (== $Candidate $e) (== $d $f)))
            (getvar (, (Inheritance $a $b) (Inheritance $Candidate $d)) $Xvar $Yvar)
            (if (== $Xvar (getvar (, (Inheritance $a $b) (Inheritance $e $f)) $Xvar $Yvar))
                (getvar (, (Inheritance $Xvar $b) (Inheritance $e $f)) $Xvar $Yvar)
                (getvar (, (Inheritance $a $Yvar) (Inheritance $e $f)) $Xvar $Yvar))))))

(= (count $pattern $cnj $Xvar $Yvar) 
    (if $cnj 
        (let $var (getvar $pattern $Xvar $Yvar) 
            (if (== $var None) 0 
                (tupleLength (collapse (match &self $pattern $var)))))
        (tupleLength (collapse (match &self $pattern 1)))))

(= (get_pattern $cnpattern)
(let (candidate $pattern $cnt) $cnpattern $pattern))

(= (support $pattern $minsup $cnj $Xvar $Yvar)
    (let $cnt (count $pattern $cnj $Xvar $Yvar)
        (if (> $cnt $minsup) (candidate $pattern $cnt) (nop))))

;; iSurprisingness formula
(= (isurprisingness $pattern)
    (let $surp
      (case $pattern (
        ((candidate (, $p1 $p2) $cnt)
        (let* (($pp1 (prob (count $p1 False $Xvar $Yvar)))
            ($pp2 (prob (count $p2 False $Xvar $Yvar)))
            ($p1p2 (* $pp1 $pp2)) ;; probability estimate 
            ($p (prob $cnt))) ;; empirical
            (/ (max (- $p $p1p2) (- $p1p2 $p)) $p)))
        ((candidate (, $p1 $p2 $p3) $cnt)
        (let* (($pp1 (prob (count $p1 False $Xvar $Yvar)))
            ($pp2 (prob (count $p2 False $Xvar $Yvar)))
            ($pp3 (prob (count $p3 False $Xvar $Yvar)))
            ($pp1p2 (prob (count (, $p1 $p2) True $Xvar $Yvar)))
            ($pp1p3 (prob (count (, $p1 $p3) True $Xvar $Yvar)))
            ($pp2p3 (prob (count (, $p2 $p3) True $Xvar $Yvar)))
            ($maxP (max (* $pp1p2 $pp3) (max (* $pp1p3 $pp2) (max (* $pp2p3 $pp1) (* $pp1 (* $pp2 $pp3))))))
            ($minP (min (* $pp1p2 $pp3) (min (* $pp1p3 $pp2) (min (* $pp2p3 $pp1) (* $pp1 (* $pp2 $pp3))))))
            ($p (prob $cnt)))
            (/ (max (- $p $maxP) (- $minP $p)) $p)))
        ($_ 0)))
     (surp $pattern $surp)))

;; Initial candidates
(= (Candidate $Xvar $Yvar)
    (match &self (Inheritance $X $Y) 
        (support (superpose ((Inheritance $Xvar $Y) (Inheritance $X $Yvar))) (minsup) False $Xvar $Yvar)))

; !(, (candidate_ptrn $Xvar $Yvar) (candidate_ptrn $Xvar $Yvar))
; !(, (candidate_ptrn $Xvar $Yvar) (candidate_ptrn $Xvar $Yvar) (candidate_ptrn $Xvar $Yvar))

;; Miner
(= (inheritance_miner $Xvar $Yvar)
    (let $comb
        (, (candidate_ptrn $Xvar $Yvar) (candidate_ptrn $Xvar $Yvar)) 
    (support $comb (minsup) True $Xvar $Yvar)))

; !(inheritance_miner $Xvar $Yvar)
; (= (isurp) (isurprisingness (inheritance_miner $Xvar $Yvar)))

; !(let (surp $p $n) (isurp) (if (> $n 0.95) $p (nop)))
; !(isurprisingness (candidate (, (Inheritance $Xvar "Concept soda drinker") (Inheritance $Xvar "Concept human")) 10))

(= (inheritance_miner_ $Xvar $Yvar)
    (let $comb  
        (, (candidate_ptrn $Xvar $Yvar) (candidate_ptrn $Xvar $Yvar) (candidate_ptrn $Xvar $Yvar))
    (support $comb (minsup) True $Xvar $Yvar)))


; !(isurprisingness (inheritance_miner_ $Xvar $Yvar))

;; getvar test
; !(getvar (, (Inheritance $Xvar (Concept "B")) (Inheritance $Xvar (Concept "B")) (Inheritance $Xvar (Concept "B"))) $Xvar $Yvar)
; !(getvar (, (Inheritance $Xvar (Concept "B")) (Inheritance $Xvar (Concept "B")) (Inheritance (Concept "A") $Yvar)) $Xvar $Yvar)
; !(getvar (, (Inheritance $Xvar (Concept "B")) (Inheritance (Concept "A") $Yvar) (Inheritance $Xvar (Concept "B"))) $Xvar $Yvar)
; !(getvar (, (Inheritance (Concept "A") $Yvar) (Inheritance $Xvar (Concept "B")) (Inheritance $Xvar (Concept "B"))) $Xvar $Yvar)
