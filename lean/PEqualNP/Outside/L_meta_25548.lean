import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25548_aux

def move (mode letter : Nat) : Nat × Nat :=
  let aligned := ((mode == 1) && letter.testBit 0 && letter.testBit 1) ||
    ((mode == 2) && letter.testBit 1)
  let hit := letter.testBit 2
  (if aligned then (if hit then 0 else 2) else 1, hit.toNat + (aligned && hit).toNat)

def scan (code length : Nat) (initial : Nat × Nat) : Nat × Nat :=
  (List.range length).foldl (fun (st : Nat × Nat) j =>
    let result := move st.1 ((code >>> (3*j)) % 8)
    (result.1,st.2+result.2)) initial

theorem scan_succ (w n : Nat) (m h : Nat) :
    scan w (n+1) (m,h) =
      let res := move m (w%8)
      scan (w/8) n (res.1,h+res.2) := by
  simp only [scan, List.range_succ_eq_map,List.foldl_cons,List.foldl_map]
  congr 2
  · funext a j
    simp only [Nat.mul_succ,Nat.shiftRight_eq_div_pow,pow_add,
      Nat.div_div_eq_div_mul]
    rw [show (2:Nat)^3=8 by decide,Nat.mul_comm (2^(3*j)) 8]

theorem listSumRange48 {α : Type} [AddCommMonoid α] (N : Nat) (f : Nat → α) :
    ((List.range N).map f).sum = ∑ i ∈ Finset.range N,f i := by
  induction N with
  | zero => simp
  | succ n ih => simp [List.range_succ,Finset.sum_range_succ,ih]

end PEqualNP.Outside.L_meta_25548_aux

namespace PEqualNP.Outside.L_meta_25548_aux

lemma stripHigh48 (n a v m h : Nat) :
    scan (8^n*a+v) n (m,h)=scan v n (m,h) := by
  induction n generalizing a v m h with
  | zero => simp [scan]
  | succ n ih =>
    rw [scan_succ,scan_succ,pow_succ,show 8^n*8*a=8*(8^n*a) by ring]
    rw [Nat.mul_add_mod_self_left,Nat.mul_add_div (by decide : 0<8)]
    exact ih .. 

lemma lastStep48 (n a v m : Nat) (ha:a<8) (hv:v<8^n) :
    scan (8^n*a+v) (n+1) (m,0) =
      let st := scan v n (m,0)
      let change := move st.1 a
      (change.1,st.2+change.2) := by
  have digit : (((8^n*a+v) >>> (3*n))%8)=a := by
    rw [Nat.shiftRight_eq_div_pow,pow_mul,show (2:Nat)^3=8 by decide,
      Nat.mul_add_div (by positivity : 0<8^n),Nat.div_eq_of_lt hv,Nat.add_zero,Nat.mod_eq_of_lt ha]
  change (List.range (n+1)).foldl _ _ = _
  rw [List.range_succ,List.foldl_append]
  change ((move (scan (8^n*a+v) n (m,0)).1 _).1,(scan (8^n*a+v) n (m,0)).2+(move (scan (8^n*a+v) n (m,0)).1 _).2) = _
  rw [stripHigh48,digit]

lemma blocksLast48 {α : Type} [AddCommMonoid α] (m n : Nat) (F : Nat → α) :
    (∑ w ∈ Finset.range (n*m), F w) = ∑ x ∈ Finset.range n, ∑ a ∈ Finset.range m,F (n*a+x) := by
  rw [Finset.sum_comm (s:=Finset.range n) (t:=Finset.range m)]
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ,Finset.sum_range_add,ih,Finset.sum_range_succ]

def delta48 (m a : Nat) : ℝ := 8*((move m a).2:ℝ)+((move m a).1:ℝ)-(m:ℝ)-5
def X48 (m n v : Nat) : ℝ := 8*((scan v n (m,0)).2:ℝ)+((scan v n (m,0)).1:ℝ)-(m:ℝ)-5*n

lemma appendX48 (n a v m : Nat) (ha:a<8) (hv:v<8^n) :
    X48 m (n+1) (8^n*a+v)=X48 m n v+delta48 (scan v n (m,0)).1 a := by
  simp only [X48,delta48,lastStep48 n a v m ha hv,Nat.cast_add,Nat.cast_one]
  ring

lemma mode48 (w n m h : Nat) (hm:m<3) : (scan w n (m,h)).1<3 := by
  induction n generalizing w m h with
  | zero => exact hm
  | succ n ih =>
    rw [scan_succ]
    apply ih
    dsimp only [move]
    split
    · split <;> decide
    · decide

lemma one48 (m : Nat) (hm : m<3) (v : ℝ) :
    (∑ a ∈ Finset.range 8,(v+delta48 m a))=8*v := by
  interval_cases m <;> norm_num [Finset.sum_range_succ,delta48,move,Nat.testBit] <;> ring

lemma twoLow48 (m : Nat) (hm : m<3) (v : ℝ) :
    8*(v^2+16) ≤ ∑ a ∈ Finset.range 8,(v+delta48 m a)^2 := by
  interval_cases m <;> norm_num [Finset.sum_range_succ,delta48,move,Nat.testBit] <;> linarith

lemma twoHigh48 (m : Nat) (hm : m<3) (v : ℝ) :
    (∑ a ∈ Finset.range 8,(v+delta48 m a)^2) ≤ 8*(v^2+40) := by
  interval_cases m <;> norm_num [Finset.sum_range_succ,delta48,move,Nat.testBit] <;> linarith

lemma fourHigh48 (m : Nat) (hm : m<3) (v : ℝ) :
    (∑ a ∈ Finset.range 8,(v+delta48 m a)^4) ≤ 8*(v^4+512*v^2+4096) := by
  interval_cases m <;> norm_num [Finset.sum_range_succ,delta48,move,Nat.testBit] <;>
    nlinarith [sq_nonneg (v-1),sq_nonneg v]

end PEqualNP.Outside.L_meta_25548_aux

namespace PEqualNP.Outside.L_meta_25548_aux

noncomputable def moment48 (m n d : Nat) : ℝ := ∑ w ∈ Finset.range (8^n), (X48 m n w)^d

lemma stepSum48 (m n : Nat) (f : ℝ→ℝ) :
    (∑ w ∈ Finset.range (8^(n+1)), f (X48 m (n+1) w)) =
      ∑ v ∈ Finset.range (8^n), ∑ a ∈ Finset.range 8, f (X48 m n v+delta48 (scan v n (m,0)).1 a) := by
  rw [pow_succ,blocksLast48]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro a ha
  rw [appendX48 _ _ _ _ (Finset.mem_range.mp ha) (Finset.mem_range.mp hv)]

theorem moments48 (m : Nat) (hm : m<3) (n : Nat) :
    moment48 m n 1=0 ∧ (8:ℝ)^n*(16*n)≤moment48 m n 2 ∧
      moment48 m n 2≤(8:ℝ)^n*(40*n) ∧ moment48 m n 4≤(8:ℝ)^n*(16384*(n:ℝ)^2) := by
  induction n with
  | zero => simp [moment48,X48,scan]
  | succ n ih =>
    obtain ⟨mean,lo,hi,kurt⟩ := ih
    have M := fun w => mode48 w n m 0 hm
    let s := Finset.range (8^n)
    let X := X48 m n
    have sizeS : (s.card:ℝ)=(8:ℝ)^n := by simp [s]
    have H0 : moment48 m (n+1) 1=0 := by
      unfold moment48
      simp only [pow_one]
      rw [stepSum48 m n (fun x => x)]
      simp only [one48 _ (M _),←Finset.mul_sum]
      have m0 : ∑ w ∈ s, X w=0 := by simpa only [moment48,pow_one] using mean
      change 8*(∑ w ∈ s, X w)=0
      rw [m0,mul_zero]
    have L : 8*(moment48 m n 2+s.card*16) ≤ moment48 m (n+1) 2 := by
      unfold moment48
      rw [stepSum48 m n (·^2)]
      have H := Finset.sum_le_sum (s:=s) (fun w _ => twoLow48 _ (M w) (X w))
      simpa only [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] using H
    have U : moment48 m (n+1) 2 ≤ 8*(moment48 m n 2+s.card*40) := by
      unfold moment48
      rw [stepSum48 m n (·^2)]
      have H := Finset.sum_le_sum (s:=s) (fun w _ => twoHigh48 _ (M w) (X w))
      simpa only [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] using H
    have F : moment48 m (n+1) 4 ≤ 8*(moment48 m n 4+512*moment48 m n 2+s.card*4096) := by
      unfold moment48
      rw [stepSum48 m n (·^4)]
      have H := Finset.sum_le_sum (s:=s) (fun w _ => fourHigh48 _ (M w) (X w))
      simpa only [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] using H
    rw [sizeS] at L U F
    simp only [pow_succ (8:ℝ),Nat.cast_succ]
    refine ⟨H0,by nlinarith,by nlinarith,?_⟩
    nlinarith [show (0:ℝ) ≤ (8:ℝ)^n by positivity,
      mul_nonneg (show (0:ℝ)≤(8:ℝ)^n by positivity) (Nat.cast_nonneg n : 0≤(n:ℝ))]

end PEqualNP.Outside.L_meta_25548_aux

namespace PEqualNP.Outside.L_meta_25548_aux

private lemma momentPoly48 (z : ℝ) : 3072*z^2 ≤ z^4+65536*|z| := by
  have p := mul_nonneg (mul_nonneg (abs_nonneg z) (sq_nonneg (|z|-32))) (show 0≤|z|+64 by positivity)
  have s : |z|^2=z^2 := sq_abs z
  have t : |z|^4=z^4 := by rw [show (4:Nat)=2*2 by decide,pow_mul,pow_mul,s]
  nlinarith only [p,s,t]

private lemma tailPoly48 (z : ℝ) (flag : Prop) [Decidable flag] (small : ¬flag → -z≤1/8) :
    |z| ≤ z+1/4+z^2/256+256*(if flag then 1 else 0) := by
  by_cases sign : 0≤z
  · rw [abs_of_nonneg sign]
    split_ifs <;> nlinarith [sq_nonneg z]
  · rw [abs_of_neg (by linarith : z<0)]
    by_cases p : flag
    · simp only [p,ite_true]
      nlinarith [sq_nonneg (z+256)]
    · simp only [p,ite_false,mul_zero,add_zero]
      nlinarith [small p,sq_nonneg z]

theorem tailFromMoments48 {N n : Nat} (hn : 0<n) (_hN : 0<N) (X : Nat→ℝ) (D : Nat→Nat)
    (hd : ∀ w<N,(D w:ℝ)=max (-X w) 0)
    (h0 : (∑ w ∈ Finset.range N,X w)=0)
    (h2l : (N:ℝ)*(16*n) ≤ ∑ w ∈ Finset.range N,(X w)^2)
    (h2u : (∑ w ∈ Finset.range N,(X w)^2) ≤ (N:ℝ)*(40*n))
    (h4 : (∑ w ∈ Finset.range N,(X w)^4) ≤ (N:ℝ)*(16384*n^2)) :
    N≤4096*((Finset.range N).filter (fun w=>n≤64*(D w)^2)).card := by
  classical
  let s := Real.sqrt n
  have hs : 0<s := Real.sqrt_pos_of_pos (by exact_mod_cast hn)
  have ss : s^2=(n:ℝ) := Real.sq_sqrt (by positivity)
  have s4 : s^4=(n:ℝ)^2 := by rw [show (4:Nat)=2*2 by decide,pow_mul,ss]
  let Z (w : Nat) := X w/s
  let T := Finset.range N
  let flag (w : Nat) := n≤64*(D w)^2
  have scaled (f : Nat→ℝ) (c : ℝ) : (∑ w ∈ T,f w/c) = (∑ w ∈ T,f w)/c := by
    simp only [div_eq_mul_inv,Finset.sum_mul]
  have avg : (∑ w ∈ T,Z w)=0 := by
    change (∑ w ∈ T,X w/s)=0
    rw [scaled,h0,zero_div]
  have zz (t : Nat) : (∑ w ∈ T,(Z w)^t) = (∑ w ∈ T,(X w)^t)/s^t := by
    simp only [Z,div_pow,scaled]
  have qlo : (N:ℝ)*16 ≤ ∑ w ∈ T,(Z w)^2 := by
    rw [zz,le_div_iff₀ (by positivity),ss]
    simpa [T,mul_assoc] using h2l
  have qhi : (∑ w ∈ T,(Z w)^2) ≤ (N:ℝ)*40 := by
    rw [zz,div_le_iff₀ (by positivity),ss]
    simpa [T,mul_assoc] using h2u
  have fhi : (∑ w ∈ T,(Z w)^4) ≤ (N:ℝ)*16384 := by
    rw [zz,div_le_iff₀ (by positivity),s4]
    simpa [T,mul_assoc] using h4
  have small (w : Nat) (hw : w∈T) (bad : ¬flag w) : -(Z w)≤1/8 := by
    have lt : ((64*(D w)^2:Nat):ℝ)<(n:ℝ) := by
      exact_mod_cast (Nat.lt_of_not_ge bad)
    push_cast at lt
    have sq : (8*(D w:ℝ))^2<s^2 := by rw [ss];nlinarith
    have lin := (sq_lt_sq₀ (by positivity : (0:ℝ)≤8*(D w:ℝ)) hs.le).mp sq
    have dx : -X w ≤ (D w:ℝ) := by rw [hd w (Finset.mem_range.mp hw)];exact le_max_left .. 
    change -(X w/s)≤1/8
    rw [←neg_div,div_le_iff₀ hs]
    linarith
  have low := Finset.sum_le_sum (s:=T) (fun w _=>momentPoly48 (Z w))
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at low
  have high := Finset.sum_le_sum (s:=T) (fun w hw=>tailPoly48 (Z w) (flag w) (small w hw))
  simp only [Finset.sum_add_distrib,scaled,←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,
    Finset.sum_boole,avg,zero_add] at high
  have count : T.card=N := Finset.card_range N
  rw [count] at high
  have cnt : 0 ≤ ((T.filter flag).card:ℝ) := by positivity
  have target : (N:ℝ) ≤ 4096*((T.filter flag).card:ℝ) := by linarith only [low,high,qlo,qhi,fhi,cnt]
  exact_mod_cast target

end PEqualNP.Outside.L_meta_25548_aux

namespace PEqualNP.Outside.L_meta_25548_aux

private lemma deficit48 (a b : Nat) : ((a-b:Nat):ℝ)=max ((a:ℝ)-b) 0 := by
  by_cases h : b≤a
  · rw [Nat.cast_sub h,max_eq_left (by exact_mod_cast (show (0:Int)≤(a:Int)-b by omega))]
  · rw [Nat.sub_eq_zero_of_le (by omega),Nat.cast_zero,max_eq_right (by exact_mod_cast (show (a:Int)-b≤0 by omega))]

theorem result48 (n m : Nat) (hn:0<n) (hm:m<3) :
    8^n ≤ 4096*((List.range (8^n)).filter (fun w =>
      let state := scan w n (m,0)
      let drop := 5*n+m-(8*state.2+state.1)
      decide (n≤64*drop^2))).length := by
  let D (w : Nat) := 5*n+m-(8*(scan w n (m,0)).2+(scan w n (m,0)).1)
  have diff (w : Nat) (_ : w<8^n) : (D w:ℝ)=max (-X48 m n w) 0 := by
    dsimp only [D,X48]
    rw [deficit48]
    push_cast
    congr 1
    ring
  obtain ⟨h0,lo,hi,four⟩ := moments48 m hm n
  have e0 : (∑ w∈Finset.range (8^n),X48 m n w)=0 := by simpa only [moment48,pow_one] using h0
  have result := tailFromMoments48 hn (by positivity : 0<8^n) (X48 m n) D diff e0
    (by simpa only [moment48,Nat.cast_pow,Nat.cast_ofNat] using lo)
    (by simpa only [moment48,Nat.cast_pow,Nat.cast_ofNat] using hi)
    (by simpa only [moment48,Nat.cast_pow,Nat.cast_ofNat] using four)
  change 8^n ≤ 4096*((List.range (8^n)).filter (fun w => decide (n≤64*(D w)^2))).length
  have eqr : (List.range (8^n)).toFinset=Finset.range (8^n) := by ext; simp
  have eq := (List.nodup_range (n:=8^n)).card_eq_countP (P:=fun w => n≤64*(D w)^2)
  rw [eqr] at eq
  rw [← List.countP_eq_length_filter,←eq]
  exact result

end PEqualNP.Outside.L_meta_25548_aux

theorem PEqualNP.Outside.L_meta_25548 :
let move := fun (mode letter : Nat) =>
    let aligned := ((mode == 1) && letter.testBit 0 && letter.testBit 1) ||
      ((mode == 2) && letter.testBit 1)
    let hit := letter.testBit 2
    (if aligned then (if hit then 0 else 2) else 1,
      hit.toNat + (aligned && hit).toNat)
  let summary := fun (initial code length : Nat) =>
    (List.range length).foldl (fun (st : Nat × Nat) digitPos =>
      let result := move st.1 ((code >>> (3 * digitPos)) % 8)
      (result.1, st.2 + result.2)) (initial, 0)
  ∀ (n initial : Nat), 0 < n → initial < 3 →
    8 ^ n ≤ 4096 * ((List.range (8 ^ n)).filter (fun word =>
      let final := summary initial word n
      let drop := 5 * n + initial - (8 * final.2 + final.1)
      decide (n ≤ 64 * drop ^ 2))).length := by
  dsimp only
  intro n initial hn hi
  exact PEqualNP.Outside.L_meta_25548_aux.result48 n initial hn hi
