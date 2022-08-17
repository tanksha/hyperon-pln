;; MeTTa port for deduction PLN rule
;; as the entail relationship, ⊢
;;
;; (≞ P ptv)
;; (≞ Q qtv)
;; (≞ R rtv)
;; (≞ (→ P Q) tv1)
;; (≞ (→ Q R) tv2)
;; ⊢
;; (≞ (→ P R) TV)
;;
;; where ptv, qtv, rtv, tv1 and tv2 are truth values of the 
;; premises P, Q, R, (→ P Q) and (→ Q R) respectively.
;; TV represents the resulting truth value of the conclusion.

;; Import TruthValue
!(import! &self "TruthValue.metta")

;; Import helper functions
!(import! &self "formula.metta")

;;;;;;;;;;;;;;;;;;;;;
;; Rule Definition ;;
;;;;;;;;;;;;;;;;;;;;;

(⊢ ;; premises 
   (≞ ($P $a) $ptv)
   (≞ ($Q $a) $qtv)
   (≞ ($R $a) $qtv)
   (≞ (→ $P $Q) $pqtv) 
   (≞ (→ $Q $R) $qrtv)
   ;; conclusion
   (≞ (→ $P $R) (formula ($ptv $qtv $rtv $pqtv $qrtv))))

;; TODO: Implement Deduction formula
(= (formula ($ptv $qtv $rtv $pqtv $qrtv)) (PrCnt 1 0))

;; 
(= (formula2 ($ptv $qtv $rtv $pqtv $qrtv))
    (let* 
        (($cP (confidence $ptv))
         ($cQ (confidence $qtv))
         ($cR (confidence $rtv))
         ($cPQ (confidence $pqtv))
         ($cQR (confidence $qrtv))
         ($sPQ (mode $pqtv))
         ($sQR (mode $qrtv))
         ;; Hacks to overcome the lack of distributional TV. If s=1
         ;; and c=0, then assign s to the mode value satisfying the
         ;; deduction consistency constraint (what a pain, let's use
         ;; 0.25 for now).
         ($sP (if (and (< 0.99 (mode $ptv)) (<= $cP 0)) 0.25 (mode $ptv)))
         ($sQ (if (and (< 0.99 (mode $qtv)) (<= $cQ 0)) 0.25 (mode $qtv)))
         ($sR (if (and (< 0.99 (mode $rtv)) (<= $cR 0)) 0.25 (mode $rtv)))
         ($alpha 0.9) ; how much confidence is lost at each deduction step
         ($zeroo (* 1 (/ 1 (pow 10 8)))))
        (if (and 
             (or (== 0 $cP) (or (== 0 $cQ) (or (== 0 $cPQ)
                (conditional-probability-consistency $sP $sQ $sPQ))))
             (or (== 0 $cQ) (or (== 0 $cR) (or (== 0 $cQR)
                (conditional-probability-consistency $sQ $sR $sQR)))))
            (if (< 0.99 (* $sQ $cQ))
                ;; Hack to overcome for the lack of distributional
                ;; TV. This covers the case where Q fully confidently
                ;; tends to 1. See formulas.metta Simple Deduction
                ;; Formula comment for more explanations. This
                ;; overlaps with the implication-introduction-rule.
                (let* (($sPR $sR)
                        ($cPR (* $alpha $cP $cR)))
                    (if (and (< $zeroo $sPR) (< $zeroo $cPR)) 
                            ;; Don't create zero knowledge. Note that
                            ;; sPR == 0 is not zero knowledge but it's 
                            ;; annoying in the current hacky situation.
                        (PrCnt $sPR $cPR)
                        (PrCnt 1 0.1)))
                ;; Branch if sQ * cQ <= 0.99
                (let* (($sPR (if (or (< 0.99 (* $sPQ $cPQ)) (< 0.99 (* $sQR $cQR)))
                                    ;; Hack to overcome for the lack of
                                    ;; distributional TV. This covers the case
                                    ;; where little is known about P and Q
                                    ;; (i.e. their strength is meaningless), yet
                                    ;; we can confidently calculate sPR because
                                    ;; sPQ and sQR are so high anyway.
                                    (* $sPQ $sQR)
                                    ;; Otherwise fall back on the naive formula
                                    (simple-deduction-strength-formula $sP $sQ $sR $sPQ $sQR)))
                       ($cPR (min $cPQ $cQR))
                       ;; Unless the 2 implication are fully confident
                       ;; decrease the confidence by some factor. I'm not
                       ;; sure how justify this for now, it's perhaps a
                       ;; bad hack.
                       ($cPR (* (if (< $cPR 0.99) $alpha 1.0) $cPR)))
                    (if (and (< $zeroo $sPR) (< $zeroo $cPR)) 
                                ;; Don't create zero knowledge. Note that
                                ;; sPR == 0 is not zero knowledge but it's 
                                ;; annoying in the current hacky situation.
                                (PrCnt $sPR $cPR)
                                (PrCnt 1 0.2))))
            (PrCnt 1 0.3))))
;; Test formula2
!(formula2 ((PrCnt 1 0) (PrCnt 1 0) (PrCnt 1 0) (PrCnt 0.345 0.91941) (PrCnt 0.345 0.91941)))

;;;;;;;;;;
;; Test ;;
;;;;;;;;;;

(= (P) (≞ (P a) (PrCnt 1 0)))
(= (Q) (≞ (Q a) (PrCnt 1 0)))
(= (R) (≞ (R a) (PrCnt 1 0)))
(= (PQ) (≞ (→ P Q) (PrCnt 0.345 0.91941)))
(= (QR) (≞ (→ Q R) (PrCnt 0.5 0.91941)))

;; Forward chain
!(let* (($p (P))
        ($q (Q))
        ($r (R))
        ($pq (PQ))
        ($qr (QR)))
    (match &self (⊢ $p $q $r $pq $qr $res) $res))

;; Backward chain
!(match &self (⊢ $p $q $r $pq $qr (≞ (→ P R) $tv)) (S $p $q $r $pq $qr $tv))
