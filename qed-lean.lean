theorem T1_1 {A B : Prop} (ha : A ) (hb : B ) : (B /\ A) /\ B := 
 and.intro (and.intro hb ha) hb


theorem T1_2 {A : Prop} (ha : A )  : A /\ A := 
 and.intro ha ha

theorem T2_1 {A B : Prop} (h : A /\ B)  : B /\ A := 
  and.intro (and.right h) (and.left h)

theorem T3_1 {A B C: Prop} (h : A )  : C \/  (A \/ B) := 
   or.inr (or.inl h) 

theorem T4_1 {A : Prop}  : A ->  ( A /\ A) := 
 assume (h : A), and.intro h h 

theorem T5_1 {A B C : Prop}  : ((A /\ B) \/ C) -> ((A /\ B) \/ C)   := 
 assume (h : ((A /\ B) \/ C) ), h

 theorem T5_2 {A B : Prop}  : B -> (A -> A)   := 
 assume (hb :B), assume (ha :A), ha 

 theorem T6_1 {A : Prop}  : A -> A   := 
 assume (ha :A), ha 

theorem T7_1 {A B : Prop}  : A -> (B -> A)  := 
  assume (ha : A), assume (hb : B), ha 

theorem T8_1 {A B : Prop} (h1 : A)  (h2 : (A -> B) ) : B:= 
  h2 h1

theorem T9_1 {A B : Prop} (h: A \/  B) : B \/  A := 
  or.elim
    h 
    (assume (h1 : A ), or.inr h1)
    (assume (h1 : B ), or.inl h1) 

theorem T9_2 {A : Prop} (h: A \/  A) : A := 
  or.elim
    h 
    (assume (h1 : A ), h1)
    (assume (h1 : A ), h1) 

theorem T10_1 {A B: Prop} (h1: A) (h2: A <-> B): B := 
  iff.elim_left h2 h1

theorem T11_1 {A B: Prop} (h: A /\ not A ) : B := 
  show B, from false.elim ((and.right h) (and.left h)) 

