; ### Algorithm Sketch

; Given a collection of data trees T, a minimum support ms and an
; initial collection of patterns C (containing at least the identity
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
; !(extend-py! nummet)

;; Parameters
(= (minsup) 1)
(= (maxiter) 10)

;; Helper function
(= (tupleLength $tuple) (if (== $tuple ()) 0 (+ 1 (tupleLength (cdr-atom $tuple)))))

;; Ignore non-strongly connected components
;; e.g (, (Inheritance $Xvar "Concept man") (Inheritance "Concept Abe" $Yvar))
;; is not strongly connected
(= (getvar (, (Inheritance $x $y) (Inheritance $z $w)) $Xvar $Yvar)
(if (and (== $x $z) (== $y $w)) None 
    (if (and (== $x $Xvar) (== $z $Xvar)) $Xvar 
        (if (and (== $y $Yvar) (== $w $Yvar)) $Yvar None))))

(= (getvar (, (, (Inheritance $a $b) (Inheritance $c $d)) (Inheritance $e $f)) $Xvar $Yvar)
    (if (== $Xvar (getvar (, (Inheritance $a $b) (Inheritance $e $f)) $Xvar $Yvar))
        (getvar (, (Inheritance $Xvar $b) (Inheritance $e $f)) $Xvar $Yvar)
        (getvar (, (Inheritance $a $Yvar) (Inheritance $e $f)) $Xvar $Yvar)))

(= (count $pattern $cnj $Xvar $Yvar) 
    (if $cnj 
        (let $var (getvar $pattern $Xvar $Yvar) 
            (if (== $var None) 0 
            (case $pattern (
            ((, $p1 $p2) (tupleLength (collapse (match &self $pattern $var))))
            ((, (, $p1 $p2) $p3) (tupleLength (collapse (match &self (, $p1 $p2 $p3) $var))))
            ((, $p3 (, $p1 $p2)) (tupleLength (collapse (match &self (, $p1 $p2 $p3) $var))))))))
        (tupleLength (collapse (match &self $pattern 1)))))

(= (get_pattern $cnpattern)
(let (candidate $pattern $cnt) $cnpattern $pattern))

(= (support $pattern $minsup $cnj $Xvar $Yvar)
    (let $cnt (count $pattern $cnj $Xvar $Yvar)
        (if (> $cnt $minsup) (candidate $pattern $cnt) (nop))))

;; Miner
(= (inheritance_miner Z $Xvar $Yvar)
    (let* ((($X $Y) (match &self (Inheritance $X $Y) ($X $Y)))
          ($A (superpose ((Inheritance $Xvar $Y) (Inheritance $X $Yvar)))))
        (support $A (minsup) False $Xvar $Yvar)))

(= (inheritance_miner (S $k) $Xvar $Yvar)
    (let $comp (, (get_pattern (inheritance_miner $k $Xvar $Yvar)) (get_pattern (inheritance_miner $k $Xvar $Yvar))) 
    (support $comp (minsup) True $Xvar $Yvar)))

!(inheritance_miner Z $Xvar $Yvar)
; !(inheritance_miner (S Z) $Xvar $Yvar)

; !(support (, (Inheritance $Xvar "Concept woman") (Inheritance $Xvar "Concept ugly")) (minsup) True $Xvar $Yvar)
; !(support (, (Inheritance $Xvar "Concept man") (Inheritance $Xvar "Concept ugly")) (minsup) True $Xvar $Yvar)
; !(support (, (Inheritance $Xvar "Concept human") (Inheritance $Xvar "Concept ugly")) (minsup) True $Xvar $Yvar)
;  ...
; [
;  (candidate (, (Inheritance $Xvar "Concept woman") (Inheritance $Xvar "Concept ugly")) 5),
;  (candidate (, (Inheritance $Xvar "Concept woman") (Inheritance $Xvar "Concept human")) 10),
;  (candidate (, (Inheritance $Xvar "Concept woman") (Inheritance $Xvar "Concept soda drinker")) 5),
;  (candidate (, (Inheritance "Concept Sophia" $Yvar) (Inheritance "Concept Lucy" $Yvar)) 3)
;  (candidate (, (Inheritance "Concept Sophia" $Yvar) (Inheritance "Concept Jassy" $Yvar)) 2)
;  (candidate (, (Inheritance $Xvar "Concept human") (Inheritance $Xvar "Concept woman")) 10),
;  (candidate (, (Inheritance $Xvar "Concept human") (Inheritance $Xvar "Concept soda drinker")) 10),
;  (candidate (, (Inheritance $Xvar "Concept human") (Inheritance $Xvar "Concept ugly")) 10),
;  (candidate (, (Inheritance $Xvar "Concept man") (Inheritance $Xvar "Concept ugly")) 5)
; ...
;; ternary
; !(support (, (, (Inheritance $Xvar "Concept human") (Inheritance $Xvar "Concept soda drinker")) (Inheritance $Xvar "Concept ugly")) (minsup) True $Xvar $Yvar)
; !(support (, (, (Inheritance $Xvar "Concept man") (Inheritance $Xvar "Concept soda drinker")) (Inheritance $Xvar "Concept ugly")) (minsup) True $Xvar $Yvar)
;
;  (candidate (, (, (Inheritance $Xvar "Concept human") (Inheritance $Xvar "Concept soda drinker")) (Inheritance $Xvar "Concept ugly")) 5)
;  (candidate (, (, (Inheritance $Xvar "Concept human") (Inheritance $Xvar "Concept soda drinker")) (Inheritance $Xvar "Concept ugly")) 10)

;; Surprisingness formula
(= (universe_size) (tupleLength (collapse (match &self (Inheritance $x $y) 1))))
(= (prob $count) (/ $count (universe_size)))

(= (isurprisingness (candidate (, $p1 $p2) $cnt))
    (let* (($subset_probs (* (prob (count $p1 False $Xvar $Yvar)) (prob (count $p2 False $Xvar $Yvar))))
           ($p (prob $cnt)))
        (surp (, $p1 $p2) (/ (max (- $p $subset_probs) (- $subset_probs $p)) $p))))

(= (isurprisingness (candidate (, (, $p1 $p2) $p3) $cnt))
    (let* (($subset_probs (* (prob (count $p1 False $Xvar $Yvar)) 
            (* (prob (count $p2 False $Xvar $Yvar)) (prob (count $p3 False $Xvar $Yvar))))
           ($p (prob $cnt))))
        (surp $pattern (/ (max (- $p $subset_probs) (- $subset_probs $p)) $p))))

; !(isurprisingness (candidate (, (Inheritance $Xvar "Concept human") (Inheritance $Xvar "Concept soda drinker")) 5))
; !(isurprisingness (candidate (, (Inheritance $Xvar "Concept man") (Inheritance $Xvar "Concept ugly")) 5))
; !(isurprisingness (candidate (, (, (Inheritance $Xvar "Concept human") (Inheritance $Xvar "Concept soda drinker")) (Inheritance $Xvar "Concept ugly")) 5))

; [(surp (, (Inheritance $Xvar "Concept man") (Inheritance $Xvar "Concept soda drinker")) 0.6666666666666666)
;  (surp (, (, (Inheritance $Xvar "Concept human") (Inheritance $Xvar "Concept soda drinker")) (Inheritance $Xvar "Concept ugly")) 0.6666666666666666)
;  (surp (, (Inheritance $Xvar "Concept human") (Inheritance $Xvar "Concept soda drinker")) 0.3333333333333333)];]
