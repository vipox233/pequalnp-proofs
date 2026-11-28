import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38907

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276809440 * 2 ^ 32 + 4209696960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x0000a61c60a2b1e4#64 ++ 0x200014c38c14563c#64 ++ 0xb813ee3ce1e7f3e7#64 ++ 0xd7027dc79c3cfe7c#64 : BitVec 256),
   (0x006586c51189942e#64 ++ 0x400cb0d8a2313285#64 ++ 0xe8ed97c711999c7f#64 ++ 0xbd1db2f8e233338f#64 : BitVec 256),
   (0x0b0a1802a6160ad0#64 ++ 0x8161430054c2c15a#64 ++ 0xdf0e1807fe1e1fff#64 ++ 0x7be1c300ffc3c3ff#64 : BitVec 256),
   (0x15b01b681be01f07#64 ++ 0x02b6036d037c03e0#64 ++ 0xf7f01ff81fe01f86#64 ++ 0xfefe03ff03fc03f0#64 : BitVec 256),
   (0x06ff40001d5d4000#64 ++ 0x00dfe80003aba800#64 ++ 0x9fffe0001fffe005#64 ++ 0xf3fffc0003fffc00#64 : BitVec 256),
   (0x27dffdb7c0000000#64 ++ 0x04fbffb6f8000000#64 ++ 0xe7ffffffe0000003#64 ++ 0xfcfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [11, 4]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000a41440000000 0x0000148288000000 0xa013ee3ce0000003 0xd4027dc79c000000

def z1 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0xb813ee3ce1e7f3e7 0xd7027dc79c3cfe7c

def z2 : W := mkw 0x006502c11189942e 0x400ca05822313285 0x48ec11c311999c7c 0x291d82386233338f

def z3 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x9fffe0001fffe005 0xf3fffc0003fffc00

def z4 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0xdf0e1807fe1e1fff 0x7be1c300ffc3c3ff

def z5 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xf7f01ff81fe01f86 0xfefe03ff03fc03f0

def z6 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z7 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0xe8ed97c711999c7f 0xbd1db2f8e233338f

def z8 : W := mkw 0x27df59a380000000 0x04fbeb3470000000 0x47ec11c300000000 0x28fd823860000000

def z9 : W := mkw 0x27dfffbfe0a2b1e4 0x24fbfff7fc14563c 0xffffffffe1e7f3e7 0xfffffffffc3cfe7c

def z10 : W := mkw 0x27dffdb7cc544000 0x04fbffb6f98a8800 0xf7ffffffee666003 0xfefffffffdcccc00

def z11 : W := mkw 0x0800000026160ad0 0x8100000004c2c15a 0xd80c10071e1e1fff 0x3b018200e3c3c3ff

def z12 : W := mkw 0x0fff5802bf5f4ad0 0x81ffeb0057ebe95a 0xdffff807ffffffff 0xfbffff00ffffffff

def z13 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0x470c1807fe181ffa 0x28e18300ffc303ff

def z14 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0x1f0e0807ee1e03f9 0x43e1c100fdc3c07f

def z15 : W := mkw 0x102002481be01f07 0x02040049037c03e0 0xf0e017c01fe01f86 0xbe1c02f803fc03f0

def z16 : W := mkw 0x2000a5b540000000 0x040014b6a8000000 0x200007f800000000 0x040000ff00000000

def z17 : W := mkw 0x0000020800a01104 0x0000004100140220 0xb813ee3801e7f387 0xd7027dc7003cfe70

def z18 : W := mkw 0x159019200a400a01 0x02b2032401480140 0x070000000e000000 0x00e0000001c00000

def z19 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xfff3fff81fe7ff87 0xfffe7fff03fcfff0

def z20 : W := mkw 0x0000024000801406 0x0000004800100280 0x600017c000001c02 0x0c0002f800000380

def z21 : W := mkw 0x020a400004144000 0x0041480000828800 0x0002600000066000 0x00004c000000cc00

def z22 : W := mkw 0x04f5400019494000 0x009ea80003292800 0x00f1e00001e1e000 0x801e3c00003c3c00

def z23 : W := mkw 0x069a40000c544000 0x00d34800018a8800 0x171260000e666000 0x42e24c0001cccc00

def z24 : W := mkw 0x226fe6d7d189942e 0x444dfcdafa313285 0xe8eff7c7f1999c7f 0xbd1dfef8fe33338f

def z25 : W := mkw 0x00002018602221c0 0x200004030c044438 0x10126838e0666380 0x42024d071c0ccc70

def z26 : W := mkw 0x0b0abe1ee6b6bbf4 0xa16157c3dcd6d77e 0xff1ffe3fffffffff 0xffe3ffc7ffffffff

def z27 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0x20000e3ce00013e2 0x040001c79c00027c

def z28 : W := mkw 0x04b0000019400000 0x0096000003280000 0x97f000001fe00004 0xf2fe000003fc0000

def z29 : W := mkw 0x0000a4146002a0e0 0x200014828c00541c 0x0803e004e007e061 0x01007c009c00fc0c

def z30 : W := mkw 0x15b0bf7c7be2bfe7 0x22b617ef8f7c57fc 0xfff3fffcffe7ffe7 0xfffe7fff9ffcfffc

def z31 : W := mkw 0x0020a61c7dfff1e4 0x200414c38fbffe3c 0xb813ee3cfffff3e7 0xd7027dc79ffffe7c

def z32 : W := mkw 0x002000001d5d4000 0x0004000003aba800 0x180000001fffe004 0x0300000003fffc00

def z33 : W := mkw 0x2100bdb7c0000000 0x042017b6f8000000 0x60001fffe0000002 0x0c0003fffc000000

def z34 : W := mkw 0x00000000200200c0 0x0000000004004018 0x10020800e0060380 0x420041001c00c070

def z35 : W := mkw 0x0000000000000000 0x0000000000000000 0x9010000001e00004 0xd2020000003c0000

def z36 : W := mkw 0x002002083dfff1e4 0x2004004107bffe3c 0x180000001ffff3e4 0x0300000003fffe7c

def z37 : W := mkw 0x1fbabf7efff6bff7 0xa3f757efdffed7fe 0xffffffffffffffff 0xffffffffffffffff

def z38 : W := mkw 0x06df400000000000 0x00dbe80000000000 0x9fffe00001e7e005 0xf3fffc00003cfc00

def z39 : W := mkw 0x24d5e7bd40a0b124 0x249abcf7a8141624 0x20f1e7f801e1e000 0x841e3cff003c3c00

def z40 : W := mkw 0x05b018001b400a00 0x00b6030003680140 0xd7f018001fe01f86 0xfafe030003fc03f0

def z41 : W := mkw 0x1fba1b6abff61fd7 0x83f7436d57fec3fa 0xfffe1ffffffe1fff 0xffffc3ffffffc3ff

def z42 : W := mkw 0x07ff58029d5d4000 0x00ffeb0053aba800 0xdffff807ffffe007 0xfbffff00fffffc00

def z43 : W := mkw 0x224fe497c0000000 0x0449fc92f8000000 0x000fe007e0000001 0x0001fc00fc000000

def z44 : W := mkw 0x37ffffffdbe01f07 0x06fffffffb7c03e0 0xf7ffffffffe01f87 0xfefffffffffc03f0

def z45 : W := mkw 0x069a40000c544000 0x00d34800018a8800 0x070000000e000000 0x00e0000001c00000

def z46 : W := mkw 0x0000000000000000 0x0000000000000000 0x9802000000060005 0x530040000000c000

def z47 : W := mkw 0x0000000000000000 0x0000000000000000 0x9813e00001e7e005 0xd3027c00003cfc00

def z48 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0x67e01ff81e001f82 0x2cfc03ff03c003f0

def z49 : W := mkw 0x0000a41440000000 0x0000148288000000 0x20000e3ce0000002 0x040001c79c000000

def z50 : W := mkw 0x0000000000000000 0x0000000000000000 0x0800000010181c7c 0x010000000203038f

def z51 : W := mkw 0x0045848500000000 0x0008b090a0000000 0xe0ed97c700000003 0xbc1db2f8e0000000

def z52 : W := mkw 0x279a7932c0000000 0x04f34f2658000000 0x07126838e0000000 0x40e24d071c000000

def z53 : W := mkw 0x27fffff7d189942e 0x44fffffefa313285 0xeffffffff1999c7f 0xfdfffffffe33338f

def z54 : W := mkw 0x030a180282000a00 0x0061430050400140 0xd70e1807fe001f87 0x7ae1c300ffc003f0

def z55 : W := mkw 0x0045a69d60a2b1e4 0x2008b4d3ac14563c 0xf8ffffffe1e7f3e7 0xff1ffffffc3cfe7c

def z56 : W := mkw 0x020aa61c64b6b1e4 0x204154c38c96d63c 0xbf1fee3cfffff3e7 0xf7e3fdc79ffffe7c

def z57 : W := mkw 0x0065848511098028 0x400cb090a2213005 0x88ed80071199807d 0xb11db000e233300f

def z58 : W := mkw 0x35f5fffd5be01f07 0x06bebfffab7c03e0 0xf7f1fff81fe01f86 0xfefe3fff03fc03f0

def z59 : W := mkw 0x06ffc6c51dddd42e 0x40dff8d8a3bbba85 0xfffff7c71ffffc7f 0xfffffef8e3ffff8f

def z60 : W := mkw 0x15b01b683be2bfe7 0x22b6036d077c57fc 0xfff01ff81fe7ffe6 0xfffe03ff03fcfffc

def z61 : W := mkw 0x2fdf59a3a6160ad0 0x85fbeb3474c2c15a 0xdfee19c7fe1e1fff 0x7bfdc338ffc3c3ff

def z62 : W := mkw 0x0065000011090000 0x000ca00002212000 0x88ed800011998005 0xb11db00002333000

def z63 : W := mkw 0x0045a49540000000 0x0008b492a8000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z64 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xeffffffff0181c7f 0xfdfffffffe03038f

def z65 : W := mkw 0x0000a61c40a01104 0x000014c388140220 0xb013ee3ce1e01387 0xd6027dc79c3c0270

def z66 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xffffffffe1e7e007 0xfffffffffc3cfc00

def z67 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0x67ec1fffe0000002 0x2cfd83fffc000000

def z68 : W := mkw 0x006500c11109040a 0x400ca01822212081 0x40ec11c310180c18 0x281d823862030183

def z69 : W := mkw 0x09001802a2020ad0 0x812003005440415a 0x40001807e0001ffa 0x08000300fc0003ff

def z70 : W := mkw 0x002002401189942e 0x4004004802313285 0x0800000011999c7c 0x010000000233338f

def z71 : W := mkw 0x0100180002000a00 0x0020030000400140 0xd70018001e001f86 0x7ae0030003c003f0

def z72 : W := mkw 0x26dfe5b7c0000000 0x04dbfcb6f8000000 0x20ffe7ffe0000001 0x841ffcfffc000000

def z73 : W := mkw 0x06ff400019400000 0x00dfe80003280000 0x97ffe0001fe00005 0xf2fffc0003fc0000

def z74 : W := mkw 0x06ffe61c7dfff1e4 0x20dffcc38fbffe3c 0xbfffee3cfffff3e7 0xf7fffdc79ffffe7c

def z75 : W := mkw 0x006502c11189140e 0x400ca05822312281 0xe0ec17c311981c1e 0xbc1d82f862330383

def z76 : W := mkw 0x15b019601b400e03 0x02b6032c036801c0 0x47e011c01e000c00 0x28fc023803c00180

def z77 : W := mkw 0x00000000200200c0 0x0000000004004018 0x98020804e00613e7 0x530041009c00c27c

def z78 : W := mkw 0x006584c51109040a 0x400cb098a2212081 0xe0ed97c710180c1b 0xbc1db2f8e2030183

def z79 : W := mkw 0x0900180282000a10 0x8120030050400142 0x4000100300000c18 0x0800020060000183

def z80 : W := mkw 0x0000a61c40a0b124 0x200014c388141624 0x2000063800000000 0x040000c700000000

def z81 : W := mkw 0x15b019601b400e03 0x02b6032c036801c0 0xe7f01ff81e000c02 0xfcfe03ff03c00180

def z82 : W := mkw 0x0000a61440809024 0x000014c288101204 0xa813ee3ce1819067 0xd5027dc79c30320c

def z83 : W := mkw 0x0f9a5802ae564ad0 0x81f34b0055cac95a 0x17126800ee666380 0x42e24d001dcccc70

def z84 : W := mkw 0x030a180280000000 0x0061430050000000 0xc70e1807e0000003 0x78e1c300fc000000

def z85 : W := mkw 0x2fdffdb7e6160ad0 0x85fbffb6fcc2c15a 0xfffffffffe1e1fff 0xffffffffffc3c3ff

def z86 : W := mkw 0x16ff42481ffd5f07 0x02dfe84903ffabe0 0x9fffe0001fffff85 0xf3fffc0003fffff0

def z87 : W := mkw 0x37ff5beb9be01f07 0x06ffeb7d737c03e0 0xf7fc1ffb1fe01f86 0xfeff83ff63fc03f0

def z88 : W := mkw 0x020a000004140000 0x0041400000828000 0x080e0000001e0001 0x0101c0000003c000

def z89 : W := mkw 0x0fba1802bf560ad0 0x81f7430057eac15a 0xdffe1807fffe1fff 0xfbffc300ffffc3ff

def z90 : W := mkw 0x0000000000000000 0x0000000000000000 0xc80c100710181c7f 0x39018200e203038f

def z91 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xfffc1fff1ff81fff 0xffff83ffe3ff03ff

def z92 : W := mkw 0x0b6f18c3971d0e1a 0xc16de31872e3a1c3 0x47ec11c31e180c18 0x28fd823863c30183

def z93 : W := mkw 0x0000840400000000 0x0000108080000000 0xa001860400000003 0x940030c080000000

def z94 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000080000001386 0x5200010000000270

def z95 : W := mkw 0x020a000004140000 0x0041400000828000 0x9f1fe0001fffe005 0xf3e3fc0003fffc00

def z96 : W := mkw 0x0900be1ee2a2bbf4 0xa12017c3dc54577e 0x60001e3fe0001ffa 0x0c0003c7fc0003ff

def z97 : W := mkw 0x0000020800a01104 0x0000004100140220 0xb0100e3801e01386 0xd60201c7003c0270

def z98 : W := mkw 0x006586cd11a9952e 0x400cb0d9a23532a5 0xf8fd9fff11f99fff 0xff1fb3ffe23f33ff

def z99 : W := mkw 0x15b0bf7c5be01f07 0x02b617ef8b7c03e0 0xf7f3fffcffe01f87 0xfefe7fff9ffc03f0

def z100 : W := mkw 0x279a793ae02221c0 0x24f34f275c044438 0x17126838e0666380 0x42e24d071c0ccc70

def z101 : W := mkw 0x0b6f9ec7b79f9efe 0xc16df3d8f6f3f3df 0xffef9fc7ff9f9fff 0xfffdf3f8fff3f3ff

def z102 : W := mkw 0x0020024011801406 0x0004004802300280 0x20e007c001800000 0x841c00f800300000

def z103 : W := mkw 0x279a7932c0000000 0x04f34f2658000000 0xe7f27ff8e0000002 0xfcfe4fff1c000000

def z104 : W := mkw 0x279aff3ee0a2b1e4 0x24f35fe7dc14563c 0xbf13ee3ce1e7f3e7 0xd7e27dc79c3cfe7c

def z105 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z106 : W := mkw 0x0065a6dd71abb5ee 0x600cb4dbae3576bd 0xf8fffffff1ffffff 0xff1ffffffe3fffff

def z107 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0x17020800ee060380 0x42e041001dc0c070

def z108 : W := mkw 0x00002018602221c0 0x200004030c044438 0x00000838e0000380 0x000001071c000070

def z109 : W := mkw 0x000086c50080942e 0x400010d8a0101285 0xe80197c701819c7f 0x9d0032f8e030338f

def z110 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0x67f017f81fe00c00 0xacfe02ff03fc0180

def z111 : W := mkw 0x1db01b6abbe21fd7 0x83b6036d577c43fa 0xf7f01fffffe01ffe 0xfefe03fffffc03ff

def z112 : W := mkw 0x06ff400019494000 0x00dfe80003292800 0x87ffe00001e1e001 0xf0fffc00003c3c00

def z113 : W := mkw 0x210019a380000000 0x0420033470000000 0x400011c300000000 0x0800023860000000

def z114 : W := mkw 0x026fc6c5159dd42e 0x404df8d8a2b3ba85 0xe8eff7c7119ffc7f 0xbd1dfef8e233ff8f

def z115 : W := mkw 0x0a0a0002a41600d0 0x814140005482c01a 0x080e0007e01e0079 0x0101c000fc03c00f

def z116 : W := mkw 0x102002483be2bfe7 0x22040049077c57fc 0x180000001fe7ffe4 0x0300000003fcfffc

def z117 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0x20e187c001818000 0x841c30f800303000

def z118 : W := mkw 0x14b0036819e01507 0x0296006d033c02a0 0x20f007f801e00000 0x841e00ff003c0000

def z119 : W := mkw 0x24d5e7bd60a2b1e4 0x249abcf7ac14563c 0xb8f3effce1e7f3e7 0xd71e7dff9c3cfe7c

def z120 : W := mkw 0x0000860400809024 0x000010c080101204 0xa801860401819067 0x950030c08030320c

def z121 : W := mkw 0x0000000000000000 0x0000000000000000 0x8013e00000000001 0xd0027c0000000000

def z122 : W := mkw 0x0020000011090000 0x0004000002212000 0x0800000011998004 0x0100000002333000

def z123 : W := mkw 0x21003932c0000000 0x0420072658000000 0x00000838e0000000 0x000001071c000000

def z124 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0xa8018e3ce18193e7 0x950031c79c30327c

def z125 : W := mkw 0x036f9ec79189942e 0x406df3d8f2313285 0xefef9fc7f1999c7f 0xfdfdf3f8fe33338f

def z126 : W := mkw 0x0800000026160ad0 0x8100000004c2c15a 0x180000001e1e1ffc 0x0300000003c3c3ff

def z127 : W := mkw 0x24d5e5b540000000 0x049abcb6a8000000 0x20f1e7f800000000 0x841e3cff00000000

def z128 : W := mkw 0x27df59a380000000 0x04fbeb3470000000 0xe7fc1ffb00000002 0xfcff83ff60000000

def z129 : W := mkw 0x15f59fed1be01f07 0x02beb3fda37c03e0 0xf7fd9fff1fe01f87 0xfeffb3ffe3fc03f0

def z130 : W := mkw 0x0a0a0002a6160ad0 0x8141400054c2c15a 0x180e0007fe1e1ffd 0x0301c000ffc3c3ff

def z131 : W := mkw 0x0000020000809024 0x0000004000101204 0x0800000001819064 0x010000000030320c

def z132 : W := mkw 0x11201b6813a01f07 0x0224036d027403e0 0xe0e01ff811801f86 0xbc1c03ff023003f0

def z133 : W := mkw 0x15b01b681be99f2f 0x42b6036d037d33e5 0xfff01ff81ff99ffe 0xfffe03ff03ff33ff

def z134 : W := mkw 0x04f5c6c519c9d42e 0x409eb8d8a3393a85 0x20f1e7c001e1e000 0x841e3cf8003c3c00

def z135 : W := mkw 0x2a4fe497e41600d0 0x8549fc92fc82c01a 0x080fe007e01e0079 0x0101fc00fc03c00f

def z136 : W := mkw 0x27fffdf7d109040a 0x44ffffbefa212081 0xe7fffffff0180c1b 0xfcfffffffe030183

def z137 : W := mkw 0x030a180280000000 0x0061430050000000 0x470c100300000000 0x28e1820060000000

def z138 : W := mkw 0x06df400000000000 0x00dbe80000000000 0x87ffe00000000001 0xf0fffc0000000000

def z139 : W := mkw 0x27fffdb7dd5d4000 0x04ffffb6fbaba800 0xffffffffffffe007 0xfffffffffffffc00

def z140 : W := mkw 0x04b0020819e01104 0x00960041033c0220 0xb7f00e381fe01386 0xf6fe01c703fc0270

def z141 : W := mkw 0x17ff5b681ffd5f07 0x02ffeb6d03ffabe0 0xfffffff81fffff87 0xffffffff03fffff0

def z142 : W := mkw 0x0b4f5802a61f4ad0 0x8169eb0054c3e95a 0xdf0ff807fe1fffff 0x7be1ff00ffc3ffff

def z143 : W := mkw 0x01001a0802a01b04 0x0020034100540360 0xf7101e381fe01f86 0xfee203c703fc03f0

def z144 : W := mkw 0x27dffff7c080942e 0x44fbfffef8101285 0xe7ffffffe0001c7b 0xfcfffffffc00038f

def z145 : W := mkw 0x14f5436819e95507 0x029ea86d033d2aa0 0x20f1e7f801e1e000 0x841e3cff003c3c00

def z146 : W := mkw 0x05b01b6011801406 0x00b6036c02300280 0xe7f01ff811801c06 0xfcfe03ff02300380

def z147 : W := mkw 0x05b0192019400000 0x00b6032403280000 0xf7f01ff81fe00006 0xfefe03ff03fc0000

def z148 : W := mkw 0x024f4000041d4000 0x0049e8000083a800 0x9f0fe0001e1fe005 0x73e1fc0003c3fc00

def z149 : W := mkw 0x0800000026160ad0 0x8100000004c2c15a 0x98020804fe1e1fff 0x530041009fc3c3ff

def z150 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0x171008381fe01f84 0x42e2010703fc03f0

def z151 : W := mkw 0x08000000241600d0 0x810000000482c01a 0x08000000001e0078 0x010000000003c00f

def z152 : W := mkw 0x05d59da500000000 0x00bab3b4a0000000 0xe7fd9fff00000003 0xfcffb3ffe0000000

def z153 : W := mkw 0x35b0bfffdbe01f07 0x06b617fffb7c03e0 0xf7f01fffffe01f86 0xfefe03fffffc03f0

def z154 : W := mkw 0x24f5e5b559494000 0x049ebcb6ab292800 0x20f1e7f801e1e000 0x841e3cff003c3c00

def z155 : W := mkw 0x07ff58001f5d4a00 0x00ffeb0003eba940 0xdffff8001fffff87 0xfbffff0003fffff0

def z156 : W := mkw 0x15b0bf7c7be2bfe7 0x22b617ef8f7c57fc 0xf7f01ffcffe01fe6 0xfefe03ff9ffc03fc

def z157 : W := mkw 0x002086c51189942e 0x400410d8a2313285 0x680017c711999c7e 0x0d0002f8e233338f

def z158 : W := mkw 0x0b0a180286140a10 0x8161430050c28142 0xdf0e10031e1e0c1d 0x7be1c20063c3c183

def z159 : W := mkw 0x15b0bf7c5be0bf27 0x22b617ef8b7c17e4 0xf7f1fff81fe1ff86 0xfefe3fff03fc3ff0

def z160 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00c100700000003 0x38018200e0000000

def z161 : W := mkw 0x00002018602221c0 0x200004030c044438 0x9812683ce06673e7 0x53024d079c0cce7c

def z162 : W := mkw 0x0045848500098028 0x4008b090a0013005 0x080d800700198079 0x0101b000e003300f

def z163 : W := mkw 0x230abdb7c0000000 0x046157b6f8000000 0xe70e1fffe0000003 0x7ce1c3fffc000000

def z164 : W := mkw 0x0020024831abb5ee 0x60040049063576bd 0x1800000011fffffc 0x03000000023fffff

def z165 : W := mkw 0x102000401b400e03 0x02040008036801c0 0x000000001e000c00 0x0000000003c00180

def z166 : W := mkw 0x2100bff7c080942e 0x442017fef8101285 0x60001fffe0001c7a 0x0c0003fffc00038f

def z167 : W := mkw 0x0065848511090000 0x000cb090a2212000 0xe8ed97c711998007 0xbd1db2f8e2333000

def z168 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0x3811e63801e7f3e4 0x87023cc7003cfe7c

def z169 : W := mkw 0x15f59fed1be99f2f 0x42beb3fda37d33e5 0xfffd9fff1ff99fff 0xffffb3ffe3ff33ff

def z170 : W := mkw 0x15901b6802a01f07 0x02b2036d005403e0 0xe7f01ff800001f82 0xfcfe03ff000003f0

def z171 : W := mkw 0x37fffdf7db400e03 0x06ffffbefb6801c0 0xe7fffffffe000c03 0xfcffffffffc00180

def z172 : W := mkw 0x0020024011801406 0x0004004802300280 0xe8ec17c711981c7f 0xbd1d82f8e233038f

def z173 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x97fc00001ff80004 0xf2ff800003ff0000

def z174 : W := mkw 0x182002483ff61fd7 0x8304004907fec3fa 0x180000001ffe1ffc 0x0300000003ffc3ff

def z175 : W := mkw 0x0065a6dd51a9b52e 0x600cb4dbaa3536a5 0xe8fdf7ff11f9fc7f 0xbd1fbeffe23f3f8f

def z176 : W := mkw 0x27fffff7d189942e 0x44fffffefa313285 0xe7ffffffe1818003 0xfcfffffffc303000

def z177 : W := mkw 0x030abe1ee0a2b1e4 0x206157c3dc14563c 0xff1ffe3fe1e7f3e7 0xffe3ffc7fc3cfe7c

def z178 : W := mkw 0x0b0a1802a41600d0 0x816143005482c01a 0xcf0e1807e01e007b 0x79e1c300fc03c00f

def z179 : W := mkw 0x01201a4013801e06 0x00240348027003c0 0xf7e01fc01f801f86 0xfefc03f803f003f0

def z180 : W := mkw 0x0000a61c40a0b124 0x200014c388141624 0xb813e63801e7e005 0xd7027cc7003cfc00

def z181 : W := mkw 0x0000020820a2b1e4 0x200000410414563c 0x1800000001e7f3e4 0x03000000003cfe7c

def z182 : W := mkw 0x102002481be01f07 0x02040049037c03e0 0x100000001fe01f84 0x0200000003fc03f0

def z183 : W := mkw 0x0490012000000000 0x0092002400000000 0x20f007f800000000 0x841e00ff00000000

def z184 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x1fec00001fffe004 0x23fd800003fffc00

def z185 : W := mkw 0x0b0a1a0aa6b6bbf4 0xa161434154d6d77e 0xdf0e1807ffffffff 0x7be1c300ffffffff

def z186 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0x3013ee38e1e7e380 0xc6027dc71c3cfc70

def z187 : W := mkw 0x006586cd31abb5ee 0x600cb0d9a63576bd 0xf8ed97c711ffffff 0xbf1db2f8e23fffff

def z188 : W := mkw 0x17ffdfed1ffddf2f 0x42fffbfda3ffbbe5 0xffffffff1fffffff 0xffffffffe3ffffff

def z189 : W := mkw 0x026f0000151d0000 0x004de00002a3a000 0x9fef80001f9f8005 0xf3fdf00003f3f000

def z190 : W := mkw 0x0b0a180286140a10 0x8161430050c28142 0x470c10031e180c18 0x28e1820063c30183

def z191 : W := mkw 0x04b0000019400000 0x0096000003280000 0x9ff3e0001fe7e005 0xf3fe7c0003fcfc00

def z192 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0x5f0c10031e1e1ffc 0x2be1820063c3c3ff

def z193 : W := mkw 0x0fff5802bf5f4ad0 0x81ffeb0057ebe95a 0x9fffe800ffffe385 0xf3fffd001ffffc70

def z194 : W := mkw 0x024f400000000000 0x0049e80000000000 0x000fe00000000001 0x0001fc0000000000

def z195 : W := mkw 0x1fba1b6a9ff41f17 0x83f7436d53fe83e2 0xf7fc1ffb1ff81f9e 0xfeff83ff63ff03f3

def z196 : W := mkw 0x00002018602221c0 0x200004030c044438 0x9813e838e1e7e385 0xd3027d071c3cfc70

def z197 : W := mkw 0x024f4000041d4000 0x0049e8000083a800 0x080fe000001fe001 0x0101fc000003fc00

def z198 : W := mkw 0x0590192000000000 0x00b2032400000000 0xe7f01ff800000002 0xfcfe03ff00000000

def z199 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0x1803e004e1e7f3e5 0x03007c009c3cfe7c

def z200 : W := mkw 0x0b0abc16e616aaf0 0xa1615782dcc2d55e 0xdf0ff807fe1fffff 0x7be1ff00ffc3ffff

def z201 : W := mkw 0x0b0abe1ee6b6bbf4 0xa16157c3dcd6d77e 0xbf13ee3cefe7f3e7 0xd7e27dc79dfcfe7c

def z202 : W := mkw 0x020a000004140000 0x0041400000828000 0x9f0e00001e1e0005 0x73e1c00003c3c000

def z203 : W := mkw 0x25d5fdb7c0000000 0x04babfb6f8000000 0x60f1ffffe0000002 0x8c1e3ffffc000000

def z204 : W := mkw 0x0b0a1802a2020ad0 0x816143005440415a 0xc70e1807e0001ffb 0x78e1c300fc0003ff

def z205 : W := mkw 0x14b0a77c59e0b527 0x229614ef8b3c16a4 0x20f1e7f801e1e000 0x841e3cff003c3c00

def z206 : W := mkw 0x0065000011090000 0x000ca00002212000 0xc8ed900711999c7f 0xb91db200e233338f

def z207 : W := mkw 0x0000a414600200c0 0x000014828c004018 0xb813ee3ce00613e7 0xd7027dc79c00c27c

def z208 : W := mkw 0x000086c50080942e 0x400010d8a0101285 0x200007c000000000 0x040000f800000000

def z209 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0xf81ffe3ff1ffffff 0xff03ffc7fe3fffff

def z210 : W := mkw 0x159019280a600b01 0x02b20325014c0160 0x171008380e600380 0x42e2010701cc0070

def z211 : W := mkw 0x06ffc4851d5dc028 0x40dff890a3abb805 0x9fffe0071fffe07d 0xf3fffc00e3fffc0f

def z212 : W := mkw 0x159019280a600b01 0x02b20325014c0160 0xf7f01ff80e600382 0xfefe03ff01cc0070

def z213 : W := mkw 0x030a180284140000 0x0061430050828000 0xdf0e1807fe1e0007 0x7be1c300ffc3c000

def z214 : W := mkw 0x0000000002000a00 0x0000000000400140 0x100000001e001f84 0x0200000003c003f0

def z215 : W := mkw 0x0000a61c40a0b124 0x200014c388141624 0x2011e63801e1e000 0x84023cc7003c3c00

def z216 : W := mkw 0x0020024011801406 0x0004004802300280 0xe0e017c011801c06 0xbc1c02f802300380

def z217 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0x60f01ff801e01f82 0x8c1e03ff003c03f0

def z218 : W := mkw 0x15b01b601bc01e07 0x02b6036c037803c0 0xe7e017c01f801c06 0xbcfc02f803f00380

def z219 : W := mkw 0x000086c50080942e 0x400010d8a0101285 0x600017c700001c7a 0x0c0002f8e000038f

def z220 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0xb8020e3ce00613e7 0x570041c79c00c27c

def z221 : W := mkw 0x3ffffffffff61fd7 0x87fffffffffec3fa 0xfffffffffffe1fff 0xffffffffffffc3ff

def z222 : W := mkw 0x022a00001d5d4000 0x0045400003aba800 0x9f0e00001fffe005 0x73e1c00003fffc00

def z223 : W := mkw 0x0900180026160ad0 0x8120030004c2c15a 0xdf0018001e1e1ffe 0x7be0030003c3c3ff

def z224 : W := mkw 0x15f51be91be91f0f 0x42bea37d237d23e1 0xf7fc1ffb1ff81f9e 0xfeff83ff63ff03f3

def z225 : W := mkw 0x24d5e5b540000000 0x049abcb6a8000000 0xa0f3effce0000003 0xd41e7dff9c000000

def z226 : W := mkw 0x0000a61c40a0b124 0x200014c388141624 0xb011ee3801e1f386 0xd6023dc7003c3e70

def z227 : W := mkw 0x069a40000c544000 0x00d34800018a8800 0x9f13e0000fe7e005 0xd3e27c0001fcfc00

def z228 : W := mkw 0x024fe414641fe0e0 0x2049fc828c83fc1c 0x080fe004e01fe061 0x0101fc009c03fc0c

def z229 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0xf8fff7c711fffc7f 0xff1ffef8e23fff8f

def z230 : W := mkw 0x006500c11109040a 0x400ca01822212081 0xc8ec11c710181c7f 0x391d8238e203038f

def z231 : W := mkw 0x224fe497c0000000 0x0449fc92f8000000 0xe0eff7c7e0000003 0xbc1dfef8fc000000

def z232 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0x27f3eff8e0000000 0xc4fe7dff1c000000

def z233 : W := mkw 0x0b2a1802bf5f4ad0 0x8165430057ebe95a 0xdf0e1807ffffffff 0x7be1c300ffffffff

def z234 : W := mkw 0x00000000200200c0 0x0000000004004018 0x18000000000613e4 0x030000000000c27c

def z235 : W := mkw 0x14b0036819e01507 0x0296006d033c02a0 0xb0f00ff801e01386 0xd61e01ff003c0270

def z236 : W := mkw 0x2490613040000000 0x04920c2608000000 0x0010603800000000 0x00020c0700000000

def z237 : W := mkw 0x1000024802a01f07 0x02000049005403e0 0x0000000000001f80 0x00000000000003f0

def z238 : W := mkw 0x279a7932cc544000 0x04f34f26598a8800 0x17126838ee666000 0x42e24d071dcccc00

def z239 : W := mkw 0x0000000000098028 0x4000000000013005 0x0800000000198078 0x010000000003300f

def z240 : W := mkw 0x06ba40001d5d4000 0x00d7480003aba800 0x1f1260001fffe004 0x43e24c0003fffc00

def z241 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0x67fdf7fb00000000 0xacffbeff60000000

def z242 : W := mkw 0x2ffffff7f79f9efe 0xc5fffffefef3f3df 0xffffffffff9f9fff 0xfffffffffff3f3ff

def z243 : W := mkw 0x11001b6802a01f07 0x0220036d005403e0 0xf7001ff81e001f86 0x7ee003ff03c003f0

def z244 : W := mkw 0x0100180000000000 0x0020030000000000 0xc700180000000002 0x78e0030000000000

def z245 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x07ec00001e180000 0x20fd800003c30000

def z246 : W := mkw 0x19001b6aa2a21fd7 0x8320036d545443fa 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z247 : W := mkw 0x030a180280000000 0x0061430050000000 0x07020800e0000000 0x40e041001c000000

def z248 : W := mkw 0x026f4000151d4000 0x004de80002a3a800 0x88efe000119fe005 0xb11dfc000233fc00

def z249 : W := mkw 0x0a0a0002a41600d0 0x814140005482c01a 0xc80e1007f01e1c7f 0x3901c200fe03c38f

def z250 : W := mkw 0x2fdffdb7e6160ad0 0x85fbffb6fcc2c15a 0xf7ffffffee060383 0xfefffffffdc0c070

def z251 : W := mkw 0x0b6fbedff7bfbffe 0xe16df7dbfef7f7ff 0xffffffffffffffff 0xffffffffffffffff

def z252 : W := mkw 0x0000860400809024 0x000010c080101204 0x2000060400001062 0x040000c08000020c

def z253 : W := mkw 0x0065000011090000 0x000ca00002212000 0x98ffe00011ffe005 0xf31ffc00023ffc00

def z254 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x8fed80001f998005 0xb1fdb00003f33000

def z255 : W := mkw 0x002000001d5d4000 0x0004000003aba800 0x000000001e180000 0x0000000003c30000

def z256 : W := mkw 0x15f51b681be91f07 0x02bea36d037d23e0 0xfffd9ff81ff99f87 0xffffb3ff03ff33f0

def z257 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0e017c000000002 0xbc1c02f800000000

def z258 : W := mkw 0x37ffffffdbe99f2f 0x46fffffffb7d33e5 0xfffffffffff99fff 0xffffffffffff33ff

def z259 : W := mkw 0x000002400080942e 0x4000004800101285 0x0000000000001c78 0x000000000000038f

def z260 : W := mkw 0x06df40000c5d4000 0x00dbe800018ba800 0x1f1fe0000e7fe001 0x43e3fc0001cffc00

def z261 : W := mkw 0x0b0a381ae6362bd0 0xa16147035cc6c57a 0xdf1e783ffe7e7fff 0x7be3cf07ffcfcfff

def z262 : W := mkw 0x08000002a00200d0 0x810000005400401a 0x00000007e0000078 0x00000000fc00000f

def z263 : W := mkw 0x34f5e7fd59e01507 0x069ebcffab3c02a0 0x20f1e7f801e00000 0x841e3cff003c0000

def z264 : W := mkw 0x0000840400008020 0x0000108080001004 0x0801800400018061 0x010030008000300c

def z265 : W := mkw 0x0045008100000000 0x0008a01020000000 0x40ec11c300000000 0x281d823860000000

def z266 : W := mkw 0x37dffdbfca600b01 0x06fbffb7f94c0160 0xf7ffffffee600383 0xfefffffffdcc0070

def z267 : W := mkw 0x15f5bffd7bebbfef 0x62beb7ffaf7d77fd 0xffffffffffffffff 0xffffffffffffffff

def z268 : W := mkw 0x15b03b787be23fc7 0x22b6076f0f7c47f8 0xf7f27ff8ffe67f86 0xfefe4fff1ffccff0

def z269 : W := mkw 0x0000201040000000 0x0000040208000000 0x00126838e0000000 0x40024d071c000000

def z270 : W := mkw 0x006584c51109842a 0x400cb098a2213085 0x48ed91c710198c79 0x291db238e203318f

def z271 : W := mkw 0x37ffffffdffd5f07 0x06fffffffbffabe0 0xffffffffffffff87 0xfffffffffffffff0

def z272 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0xa013ee3ce00013e3 0xd4027dc79c00027c

def z273 : W := mkw 0x0045848500000000 0x0008b090a0000000 0x000d800700000001 0x0001b000e0000000

def z274 : W := mkw 0x17ff59601f5d4e03 0x02ffeb2c03eba9c0 0x47ec11c01e180c00 0x28fd823803c30180

def z275 : W := mkw 0x0065a6d55189942e 0x400cb4daaa313285 0xe8fffffff1999c7f 0xfd1ffffffe33338f

def z276 : W := mkw 0x0a4f4002a41f40d0 0x8149e8005483e81a 0x080fe007e01fe079 0x0101fc00fc03fc0f

def z277 : W := mkw 0x1000036800a01507 0x0200006d001402a0 0x200007f800000000 0x040000ff00000000

def z278 : W := mkw 0x1b2a1a4abff61fd7 0x8365434957fec3fa 0xdf0e1807fffe1fff 0x7be1c300ffffc3ff

def z279 : W := mkw 0x07df592000000000 0x00fbeb2400000000 0xe7fffff800000003 0xfcffffff00000000

def z280 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0x570e1803fe1e0f98 0x6ae1c3007fc3c1f3

def z281 : W := mkw 0x27ffffbffdfff1e4 0x24fffff7ffbffe3c 0xfffffffffffff3e7 0xfffffffffffffe7c

def z282 : W := mkw 0x000000c10000040a 0x4000001820000081 0x400011c300000c18 0x0800023860000183

def z283 : W := mkw 0x2590bdb7c0000000 0x04b217b6f8000000 0xe7f01fffe0000002 0xfcfe03fffc000000

def z284 : W := mkw 0x06ffc6c51189942e 0x40dff8d8a2313285 0xeffff7c711999c7f 0xfdfffef8e233338f

def z285 : W := mkw 0x0000000000000000 0x0000000000000000 0x400c100310180c18 0x2801820062030183

def z286 : W := mkw 0x04f5400019494000 0x009ea80003292800 0x00e0000000000000 0x001c000000000000

def z287 : W := mkw 0x0045868500809024 0x0008b0d0a0101204 0xe8ed97c701819067 0xbd1db2f8e030320c

def z288 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0x1f020800fe1e1ffc 0x43e041001fc3c3ff

def z289 : W := mkw 0x11201b681be01f07 0x0224036d037c03e0 0x70001ff81fe01f86 0x0e0003ff03fc03f0

def z290 : W := mkw 0x079a192280000000 0x00f3432450000000 0xe7fe1fffe0000003 0xfcffc3fffc000000

def z291 : W := mkw 0x0a0aa61ee4b6b1f4 0xa14154c3dc96d63e 0xb81fee3fe1fff3ff 0xd703fdc7fc3ffe7f

def z292 : W := mkw 0x234ffc97c0000000 0x0469ff92f8000000 0xc70ff807e0000003 0x78e1ff00fc000000

def z293 : W := mkw 0x0000000000000000 0x0000000000000000 0x80020804e0000003 0x500041009c000000

def z294 : W := mkw 0x0065a61c71abb1e4 0x200cb4c38e35763c 0xb8ffee3cf1fff3e7 0xf71ffdc79e3ffe7c

def z295 : W := mkw 0x000000000c544000 0x00000000018a8800 0x100000000e666000 0x0200000001cccc00

def z296 : W := mkw 0x234ffdb7c0000000 0x0469ffb6f8000000 0x600fffffe0000003 0x0c01fffffc000000

def z297 : W := mkw 0x0045848500000000 0x0008b090a0000000 0x20e187c000000000 0x841c30f800000000

def z298 : W := mkw 0x0100180280000000 0x0020030050000000 0x40001807e0000002 0x08000300fc000000

def z299 : W := mkw 0x069ae61c6cf6f1e4 0x20d35cc38d9ede3c 0xbf13ee3cefe7f3e7 0xd7e27dc79dfcfe7c

def z300 : W := mkw 0x08200240379f9efe 0xc104004806f3f3df 0x180000001f9f9ffc 0x0300000003f3f3ff

def z301 : W := mkw 0x11001b6802a01f07 0x0220036d005403e0 0x60001ff800001f82 0x0c0003ff000003f0

def z302 : W := mkw 0x0045848500000000 0x0008b090a0000000 0xe8ed97c710181c7f 0xbd1db2f8e203038f

def z303 : W := mkw 0x0000860400809024 0x000010c080101204 0xe80d960711999c7f 0xbd01b2c0e233338f

def z304 : W := mkw 0x0000020800a01104 0x0000004100140220 0x1000000001e01384 0x02000000003c0270

def z305 : W := mkw 0x0000020820a2b1e4 0x200000410414563c 0x00000000000013e0 0x000000000000027c

def z306 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0x57e011c01fe01f84 0x2afc023803fc03f0

def z307 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x17f3e0000fe7e000 0xc2fe7c0001fcfc00

def z308 : W := mkw 0x1f9a192aae760bd1 0x83f3432555cec17a 0x17120838ee660380 0x42e241071dccc070

def z309 : W := mkw 0x27dffdb7c4140000 0x04fbffb6f8828000 0xfffffffffe1e0007 0xffffffffffc3c000

def z310 : W := mkw 0x26ffe497dd5d4000 0x04dffc92fbaba800 0x9fffe007ffffe005 0xf3fffc00fffffc00

def z311 : W := mkw 0x0b0abe1ee6b6bbf4 0xa16157c3dcd6d77e 0xff0e1e3ffe1e1fff 0x7fe1c3c7ffc3c3ff

def z312 : W := mkw 0x2f9a7932e6160ad0 0x85f34f265cc2c15a 0x17126838ee060380 0x42e24d071dc0c070

def z313 : W := mkw 0x0020000019494000 0x0004000003292800 0x0000000001e1e000 0x00000000003c3c00

def z314 : W := mkw 0x1020a65c7be2bfe7 0x220414cb8f7c57fc 0xb813ee3cffe7ffe7 0xd7027dc79ffcfffc

def z315 : W := mkw 0x069a60186c7661c0 0x20d34c030d8ecc38 0x17126838ee666380 0x42e24d071dcccc70

def z316 : W := mkw 0x27dfffbfc0a0b124 0x24fbfff7f8141624 0xe7ffffffe1e1e003 0xfcfffffffc3c3c00

def z317 : W := mkw 0x2100bfbfe0a2b1e4 0x242017f7fc14563c 0x60001fffe00013e2 0x0c0003fffc00027c

def z318 : W := mkw 0x06ff40003d5f40c0 0x00dfe80007abe818 0x9fffe804fffff3e7 0xf3fffd009ffffe7c

def z319 : W := mkw 0x0eff40003f5f4ad0 0x81dfe80007ebe95a 0x9fffe0001ffffffd 0xf3fffc0003ffffff

def z320 : W := mkw 0x1100bf7c62a2bfe7 0x222017ef8c5457fc 0xf813fffce1e7ffe7 0xdf027fff9c3cfffc

def z321 : W := mkw 0x06ffc6c51dddd42e 0x40dff8d8a3bbba85 0xefed97c71f999c7f 0xbdfdb2f8e3f3338f

def z322 : W := mkw 0x15901b680ae01f07 0x02b2036d015c03e0 0x77101ff80e601f82 0x4ee203ff01cc03f0

def z323 : W := mkw 0x0000a41c602221c0 0x200014838c044438 0xb013ee3ce0666383 0xd6027dc79c0ccc70

def z324 : W := mkw 0x0a0a0002a41600d0 0x814140005482c01a 0x9f0e0007fe1e007d 0x73e1c000ffc3c00f

def z325 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0x4f0e1007fe1e0c79 0x29e1c200ffc3c18f

def z326 : W := mkw 0x37ffffffd9e01507 0x06fffffffb3c02a0 0xe7ffffffe1e00003 0xfcfffffffc3c0000

def z327 : W := mkw 0x002000001d5d4000 0x0004000003aba800 0x9813e0001fffe005 0xd3027c0003fffc00

def z328 : W := mkw 0x04f5e61c79ebf1e4 0x209ebcc38f3d7e3c 0xb8f3ee3ce1e7f3e7 0xd71e7dc79c3cfe7c

def z329 : W := mkw 0x09001802a2020ad0 0x812003005440415a 0xd7001807fe001ffe 0x7ae00300ffc003ff

def z330 : W := mkw 0x27dffdb7c41d4000 0x04fbffb6f883a800 0xefffffffe01fe003 0xfdfffffffc03fc00

def z331 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0x38000e3ce1e7f3e6 0x070001c79c3cfe7c

def z332 : W := mkw 0x17ff59281f7d4b01 0x02ffeb2503efa960 0x9fffe8381fffe385 0xf3fffd0703fffc70

def z333 : W := mkw 0x0b2a1a42b79f9efe 0xc165434856f3f3df 0xdf0e1807ff9f9fff 0x7be1c300fff3f3ff

def z334 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000100700001c7a 0x08000200e000038f

def z335 : W := mkw 0x0000a41440000000 0x0000148288000000 0xb813ee3ce1e7e007 0xd7027dc79c3cfc00

def z336 : W := mkw 0x279a7932c0000000 0x04f34f2658000000 0xc71e783fe0000003 0x78e3cf07fc000000

def z337 : W := mkw 0x0000a4146002a0e0 0x200014828c00541c 0xa813ee3ce007e063 0xd5027dc79c00fc0c

def z338 : W := mkw 0x06df400000000000 0x00dbe80000000000 0x07ec000000000000 0x20fd800000000000

def z339 : W := mkw 0x0000860400809024 0x000010c080101204 0xb813e60401e7f067 0xd7027cc0803cfe0c

def z340 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0xdffff0071ffffc7f 0xfbfffe00e3ffff8f

def z341 : W := mkw 0x0a6f86c7b59f94fe 0xc14df0d8f6b3f29f 0xe8ef97c7f19f9c7f 0xbd1df2f8fe33f38f

def z342 : W := mkw 0x0065a6dd71abb5ee 0x600cb4dbae3576bd 0xb8f3effce1e7f3e7 0xd71e7dff9c3cfe7c

def z343 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0x2813e63ce1e7e061 0x85027cc79c3cfc0c

def z344 : W := mkw 0x2fdffdb7e41600d0 0x85fbffb6fc82c01a 0xefffffffe01e007b 0xfdfffffffc03c00f

def z345 : W := mkw 0x224fe69fe0a2b1e4 0x2449fcd3fc14563c 0xb81fee3fe1e7f3e7 0xd703fdc7fc3cfe7c

def z346 : W := mkw 0x2fdffdb7c6140a10 0x85fbffb6f8c28142 0xe7fffffffe180c1b 0xfcffffffffc30183

def z347 : W := mkw 0x0800000022020ad0 0x810000000440415a 0x0000000000001ff8 0x00000000000003ff

def z348 : W := mkw 0x102002481ffd5f07 0x0204004903ffabe0 0x180000001fffff84 0x0300000003fffff0

def z349 : W := mkw 0x06ff42081dfd5104 0x00dfe84103bfaa20 0xbfffee381ffff387 0xf7fffdc703fffe70

def z350 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0x37f00ff80fe00380 0xc6fe01ff01fc0070

def z351 : W := mkw 0x0100180002000a00 0x0020030000400140 0x4000180000001f82 0x08000300000003f0

def z352 : W := mkw 0x27fffdb7d9400000 0x04ffffb6fb280000 0xf7ffffffffe00007 0xfefffffffffc0000

def z353 : W := mkw 0x00000008202221c0 0x2000000104044438 0x1000000000666380 0x02000000000ccc70

def z354 : W := mkw 0x27df59a380000000 0x04fbeb3470000000 0xc7ee19c7e0000003 0x78fdc338fc000000

def z355 : W := mkw 0x0ffffe1efffffbf4 0xa1ffffc3dfffff7e 0xfffffe3fffffffff 0xffffffc7ffffffff

def z356 : W := mkw 0x04b000001d5d4000 0x0096000003aba800 0x9ff000001fffe004 0xf3fe000003fffc00

def z357 : W := mkw 0x002002401189942e 0x4004004802313285 0x0000000001818000 0x0000000000303000

def z358 : W := mkw 0x04f586c519c9942e 0x409eb0d8a3393285 0xfffd97c71ff99c7f 0xffffb2f8e3ff338f

def z359 : W := mkw 0x15b019681b600f03 0x02b6032d036c01e0 0x57f019f81e600f80 0x6afe033f03cc01f0

def z360 : W := mkw 0x020a000000000000 0x0041400000000000 0x870e000000000001 0x70e1c00000000000

def z361 : W := mkw 0x09659ec7b38b9efe 0xc12cb3d8f67173df 0xe8ed9fc7f1999fff 0xbd1db3f8fe3333ff

def z362 : W := mkw 0x2045e49540000000 0x0408bc92a8000000 0x0001e00000000000 0x00003c0000000000

def z363 : W := mkw 0x14b003681be01f07 0x0296006d037c03e0 0x30f007f81fe01f84 0x861e00ff03fc03f0

def z364 : W := mkw 0x0000000000000000 0x0000000000000000 0x1800000001e7e004 0x03000000003cfc00

def z365 : W := mkw 0x2100bdb7c0000000 0x042017b6f8000000 0xe013ffffe0000003 0xdc027ffffc000000

def z366 : W := mkw 0x0100180022020ac0 0x0020030004404158 0xdf021804fe061fe7 0x7be043009fc0c3fc

def z367 : W := mkw 0x0000860c20a2b1e4 0x200010c18414563c 0xb801860401e7f3e7 0x970030c0803cfe7c

def z368 : W := mkw 0x000000002002a0e0 0x200000000400541c 0x080000000007e060 0x010000000000fc0c

def z369 : W := mkw 0x0000221860a231c4 0x200004430c144638 0xb0126e38e1e67386 0xd6024dc71c3cce70

def z370 : W := mkw 0x04f540001d5d4000 0x009ea80003aba800 0x18f1e0001fffe004 0x831e3c0003fffc00

def z371 : W := mkw 0x0590192002000a00 0x00b2032400400140 0xf7f01ff81e001f86 0xfefe03ff03c003f0

def z372 : W := mkw 0x17ba5b681ff45f07 0x02f74b6d03fe8be0 0xf7f27ff81fe67f86 0xfefe4fff03fccff0

def z373 : W := mkw 0x24f5e7f55189942e 0x449ebcfeaa313285 0x20f1e7f801818000 0x841e3cff00303000

def z374 : W := mkw 0x09001802a2020ad0 0x812003005440415a 0xd8021807e0061fff 0x5b004300fc00c3ff

def z375 : W := mkw 0x0a4f8487a41f80f8 0xc149f090f483f01f 0x080f8007e01f8079 0x0101f000fc03f00f

def z376 : W := mkw 0x102002481be99f2f 0x42040049037d33e5 0x180000001ff99ffc 0x0300000003ff33ff

def z377 : W := mkw 0x0000a6dd60a2b5ee 0x600014dbac1456bd 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z378 : W := mkw 0x0045000000090000 0x0008a00000012000 0x080d800000198001 0x0101b00000033000

def z379 : W := mkw 0x0020024011801406 0x0004004802300280 0x0000000011801c04 0x0000000002300380

def z380 : W := mkw 0x2fdffdb7e2020ad0 0x85fbffb6fc40415a 0xe7ffffffe0001ffb 0xfcfffffffc0003ff

def z381 : W := mkw 0x1fba19629f540e13 0x83f7432c53ea81c2 0x47ec11c31e180c18 0x28fd823863c30183

def z382 : W := mkw 0x2fdfffbfe6b6bbf4 0xa5fbfff7fcd6d77e 0xffffffffffffffff 0xffffffffffffffff

def z383 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x9fee00001e1e0005 0x73fdc00003c3c000

def z384 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000100010001c06 0x3800020002000380

def z385 : W := mkw 0x27ff7932dd5d4000 0x04ffef265baba800 0x9fffe838ffffe005 0xf3fffd071ffffc00

def z386 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0x2011ee3ce1e1f3e2 0x84023dc79c3c3e7c

def z387 : W := mkw 0x0000020820a2b1e4 0x200000410414563c 0x9813e00001e7f3e5 0xd3027c00003cfe7c

def z388 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0x60ed97c311998c18 0xac1db2f862333183

def z389 : W := mkw 0x0a0a0002a41600d0 0x814140005482c01a 0x00020000e0060000 0x000040001c00c000

def z390 : W := mkw 0x27dffdb7c0098028 0x44fbffb6f8013005 0xefffffffe019807b 0xfdfffffffc03300f

def z391 : W := mkw 0x0a0a000284140010 0x8141400050828002 0x000c000300180018 0x0001800060030003

def z392 : W := mkw 0x1590bf3c6ae2bbe5 0x22b217e78d5c577c 0xbf13ee3cefe7f3e7 0xd7e27dc79dfcfe7c

def z393 : W := mkw 0x0000a4146002a0e0 0x200014828c00541c 0x00000004e0000060 0x000000009c00000c

def z394 : W := mkw 0x006586c5318b94ee 0x400cb0d8a631729d 0xf8ef9fc7f19f9fff 0xff1df3f8fe33f3ff

def z395 : W := mkw 0x27dffdb7e00200c0 0x04fbffb6fc004018 0xffffffffe00613e7 0xfffffffffc00c27c

def z396 : W := mkw 0x06ffc6c51dddd42e 0x40dff8d8a3bbba85 0xbfffe7c01fffe005 0xf7fffcf803fffc00

def z397 : W := mkw 0x26dfe497c0000000 0x04dbfc92f8000000 0x87ffe007e0000001 0xf0fffc00fc000000

def z398 : W := mkw 0x0000a61c40a0b124 0x200014c388141624 0xa013ee3ce1e1e003 0xd4027dc79c3c3c00

def z399 : W := mkw 0x002002401189942e 0x4004004802313285 0xe8e017c011999c7e 0xbd1c02f80233338f

def z400 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0xe0ed97c701818003 0xbc1db2f8e0303000

def z401 : W := mkw 0x17ba1b6a9be01f07 0x02f7436d537c03e0 0xf7fe1fffffe01f87 0xfeffc3fffffc03f0

def z402 : W := mkw 0x0590bd3440000000 0x00b217a688000000 0xe7f3fffce0000003 0xfcfe7fff9c000000

def z403 : W := mkw 0x0000000000000000 0x0000000000000000 0x880c000010180005 0x3101800002030000

def z404 : W := mkw 0x0b6f1802b71f0ad0 0x816de30056e3e15a 0xdfef9807ff9f9fff 0xfbfdf300fff3f3ff

def z405 : W := mkw 0x0a0a000026160ad0 0x8141400004c2c15a 0x9f0e00001e1e1ffd 0x73e1c00003c3c3ff

def z406 : W := mkw 0x27dffdb7c2000a00 0x04fbffb6f8400140 0xf7fffffffe001f87 0xfeffffffffc003f0

def z407 : W := mkw 0x09001802a2020ad0 0x812003005440415a 0x00000800e0000380 0x000001001c000070

def z408 : W := mkw 0x09009ec7a2829efe 0xc12013d8f45053df 0x60001fc7e0001ffa 0x0c0003f8fc0003ff

def z409 : W := mkw 0x004586c50089942e 0x4008b0d8a0113285 0x680d97c700199c7b 0x0d01b2f8e003338f

def z410 : W := mkw 0x0020000019400000 0x0004000003280000 0x100000001fe00004 0x0200000003fc0000

def z411 : W := mkw 0x020a000280000000 0x0041400050000000 0x000e0007e0000001 0x0001c000fc000000

def z412 : W := mkw 0x00000000200200c0 0x0000000004004018 0x08020004e0060061 0x010040009c00c00c

def z413 : W := mkw 0x034f9c8780000000 0x0069f390f0000000 0xe7ef9fc7e0000003 0xfcfdf3f8fc000000

def z414 : W := mkw 0x04f5c6c519c9d42e 0x409eb8d8a3393a85 0xe8fdf7c711f9fc7f 0xbd1fbef8e23f3f8f

def z415 : W := mkw 0x0000000000000000 0x0000000000000000 0x0011e00001e1e000 0x80023c00003c3c00

def z416 : W := mkw 0x2900bdb7e2020ad0 0x852017b6fc40415a 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z417 : W := mkw 0x26ffe5b55d5d4000 0x04dffcb6ababa800 0xbfffe7f81fffe005 0xf7fffcff03fffc00

def z418 : W := mkw 0x006586c511801406 0x000cb0d8a2300280 0xe0ed97c711801c07 0xbc1db2f8e2300380

def z419 : W := mkw 0x279a592280000000 0x04f34b2450000000 0x0700000000000000 0x00e0000000000000

def z420 : W := mkw 0x0000000000000000 0x0000000000000000 0x0803e0000007e001 0x01007c000000fc00

def z421 : W := mkw 0x11001b6802a01f07 0x0220036d005403e0 0xf0101ff801e01f86 0xde0203ff003c03f0

def z422 : W := mkw 0x0045400000094000 0x0008a80000012800 0x0001e0000001e000 0x00003c0000003c00

def z423 : W := mkw 0x0100192000000000 0x0020032400000000 0x60001ff800000002 0x0c0003ff00000000

def z424 : W := mkw 0x0000020800a0b124 0x2000004100141624 0x0000000001e1e000 0x00000000003c3c00

def z425 : W := mkw 0x24d541a100000000 0x049aa83420000000 0x00e001c000000000 0x001c003800000000

def z426 : W := mkw 0x1fba1962bf560ed3 0x83f7432c57eac1da 0xdfee19c7fe1e1fff 0x7bfdc338ffc3c3ff

def z427 : W := mkw 0x224fe497c41d4000 0x0449fc92f883a800 0x080fe007e01fe001 0x0101fc00fc03fc00

def z428 : W := mkw 0x0fff58029f5d4a10 0x81ffeb0053eba942 0xdffff0031fffec1d 0xfbfffe0063fffd83

def z429 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0100e3800000002 0xd40201c700000000

def z430 : W := mkw 0x0020000011000000 0x0004000002200000 0x80e0000011800004 0xb01c000002300000

def z431 : W := mkw 0x0000000004140000 0x0000000000828000 0x180000001e1e0004 0x0300000003c3c000

def z432 : W := mkw 0x27ff59a39d5d4000 0x04ffeb3473aba800 0x47ec11c31e180000 0x28fd823863c30000

def z433 : W := mkw 0x082000003f5f4ad0 0x8104000007ebe95a 0x180000001ffffffc 0x0300000003ffffff

def z434 : W := mkw 0x006502401189942e 0x400ca04802313285 0x88ed800011999c7d 0xb11db0000233338f

def z435 : W := mkw 0x14f587ed19e9952f 0x429eb0fda33d32a5 0xe8fd97ff11f99c7f 0xbd1fb2ffe23f338f

def z436 : W := mkw 0x0000020800a01104 0x0000004100140220 0x2010063801e00000 0x840200c7003c0000

def z437 : W := mkw 0x17ff59601f5d4e03 0x02ffeb2c03eba9c0 0xdffff1c01fffec05 0xfbfffe3803fffd80

def z438 : W := mkw 0x0590192000000000 0x00b2032400000000 0x47e011c000000000 0x28fc023800000000

def z439 : W := mkw 0x27fffff7d1801406 0x04fffffefa300280 0xe7fffffff1801c07 0xfcfffffffe300380

def z440 : W := mkw 0x030a180006140a00 0x0061430000c28140 0xdf0e18001e1e1f87 0x7be1c30003c3c3f0

def z441 : W := mkw 0x00000000200200c0 0x0000000004004018 0x00000804e00013e2 0x000001009c00027c

def z442 : W := mkw 0x09001802a2020ad0 0x812003005440415a 0xc80c1807f0181fff 0x39018300fe0303ff

def z443 : W := mkw 0x1f9a192aae760bd1 0x83f3432555cec17a 0xdf1e183ffe7e1fff 0x7be3c307ffcfc3ff

def z444 : W := mkw 0x00000000041d4000 0x000000000083a800 0x08000000001fe000 0x010000000003fc00

def z445 : W := mkw 0x0800a61c66b6bbf4 0xa10014c38cd6d77e 0xb813ee3cffffffff 0xd7027dc79fffffff

def z446 : W := mkw 0x379a793aca600b01 0x06f34f27594c0160 0x17126838ee600380 0x42e24d071dcc0070

def z447 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800000400001067 0x110000008000020c

def z448 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0xd7021800fe061f86 0x7ae043001fc0c3f0

def z449 : W := mkw 0x06ffc4851d5d4000 0x00dff890a3aba800 0xfffff7c71fffe007 0xfffffef8e3fffc00

def z450 : W := mkw 0x024f4000041d4000 0x0049e8000083a800 0x000c000000180000 0x0001800000030000

def z451 : W := mkw 0x0b0a180286140a10 0x8161430050c28142 0xd70c18031e181f9e 0x7ae1830063c303f3

def z452 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0x071fe83fe0000001 0x40e3fd07fc000000

def z453 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0xdf1ff807ffffffff 0xfbe3ff00ffffffff

def z454 : W := mkw 0x030a1802a00200c0 0x0061430054004018 0xdf0e1807e00613e7 0x7be1c300fc00c27c

def z455 : W := mkw 0x0000848500000000 0x00001090a0000000 0x600017c700000002 0x0c0002f8e0000000

def z456 : W := mkw 0x220a6012c0000000 0x04414c0258000000 0x00026000e0000000 0x00004c001c000000

def z457 : W := mkw 0x224fe497c0098028 0x4449fc92f8013005 0x080fe007e0198079 0x0101fc00fc03300f

def z458 : W := mkw 0x06ffc6041dddd024 0x00dff8c083bbba04 0xbfffe6041ffff067 0xf7fffcc083fffe0c

def z459 : W := mkw 0x0b0a180286140a10 0x8161430050c28142 0x070000000e000000 0x00e0000001c00000

def z460 : W := mkw 0x15b019601b400e03 0x02b6032c036801c0 0xd7e019c01e001f86 0x7afc033803c003f0

def z461 : W := mkw 0x024fc485041dc028 0x4049f890a083b805 0x080fe007001fe079 0x0101fc00e003fc0f

def z462 : W := mkw 0x0b6f9ec7979d9e3e 0xc16df3d8f2f3b3c7 0xefed97c71f999c7f 0xbdfdb2f8e3f3338f

def z463 : W := mkw 0x0fff5802bf5f4ad0 0x81ffeb0057ebe95a 0xdfee1807fe1e1fff 0x7bfdc300ffc3c3ff

def z464 : W := mkw 0x002086c51180942e 0x400410d8a2301285 0xe0e017c711801c7e 0xbc1c02f8e230038f

def z465 : W := mkw 0x0045848500098028 0x4008b090a0013005 0xe8ed97c70019807b 0xbd1db2f8e003300f

def z466 : W := mkw 0x0000860400809024 0x000010c080101204 0x2001860001818000 0x840030c000303000

def z467 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x07fde0001ff9e000 0xa0ffbc0003ff3c00

def z468 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0x47eff1c7e0000001 0x28fdfe38fc000000

def z469 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0x30126e3ce06673e2 0x46024dc79c0cce7c

def z470 : W := mkw 0x020a000004140000 0x0041400000828000 0xdf0e10071e1e1c7f 0x7be1c200e3c3c38f

def z471 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0x9f0e0800fe1e0385 0x73e1c1001fc3c070

def z472 : W := mkw 0x224f408380000000 0x0449e81070000000 0x000c000300000000 0x0001800060000000

def z473 : W := mkw 0x27ffdfe79189942e 0x44fffbfcf2313285 0xefed97c711999c7f 0xbdfdb2f8e233338f

def z474 : W := mkw 0x0000848500008028 0x40001090a0001005 0x0000000700000078 0x00000000e000000f

def z475 : W := mkw 0x11009fed02a09f2f 0x422013fda05413e5 0x60001fff00001ffa 0x0c0003ffe00003ff

def z476 : W := mkw 0x0000a41c6022a1e0 0x200014838c04543c 0x1813e83ce067e3e1 0x43027d079c0cfc7c

def z477 : W := mkw 0x0000a6dd60a2b5ee 0x600014dbac1456bd 0xf813ffffe1e7ffff 0xdf027ffffc3cffff

def z478 : W := mkw 0x0100180002000a00 0x0020030000400140 0xdf0c18071e181fff 0x7be18300e3c303ff

def z479 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x87ffe0001e180001 0xf0fffc0003c30000

def z480 : W := mkw 0x0490000008400000 0x0092000001080000 0x171000000e600000 0x42e2000001cc0000

def z481 : W := mkw 0x07df580280000000 0x00fbeb0050000000 0xc7fff807e0000003 0xf8ffff00fc000000

def z482 : W := mkw 0x06ff42083dfff1e4 0x20dfe84107bffe3c 0x9fffe0001ffff3e5 0xf3fffc0003fffe7c

def z483 : W := mkw 0x16ff43681dfd5507 0x02dfe86d03bfaaa0 0xbfffe7f81fffe005 0xf7fffcff03fffc00

def z484 : W := mkw 0x04f5000019490000 0x009ea00003292000 0x9ffd80001ff98005 0xf3ffb00003ff3000

def z485 : W := mkw 0x15901b280ae01b05 0x02b20365015c0360 0xb7100e380fe01386 0xd6e201c701fc0270

def z486 : W := mkw 0x14b0016019400403 0x0296002c03280080 0x00e001c000000000 0x001c003800000000

def z487 : W := mkw 0x15b01b6819e01507 0x02b6036d033c02a0 0xe7f01ff801e00002 0xfcfe03ff003c0000

def z488 : W := mkw 0x0590bf3c60a2b1e4 0x20b217e78c14563c 0xfff3fffce1e7f3e7 0xfffe7fff9c3cfe7c

def z489 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0x60ec17c710181c7a 0x2c1d82f8e203038f

def z490 : W := mkw 0x06ff40c11d5d440a 0x40dfe81823aba881 0x47ec11c31e180c18 0x28fd823863c30183

def z491 : W := mkw 0x2100bfbfe0a2b1e4 0x242017f7fc14563c 0xf813ffffe1e7f3e7 0xdf027ffffc3cfe7c

def z492 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x0fefe0001e1fe001 0x21fdfc0003c3fc00

def z493 : W := mkw 0x1100bf7c62a2bfe7 0x222017ef8c5457fc 0x60001ffce0001fe2 0x0c0003ff9c0003fc

def z494 : W := mkw 0x024fe61c64bff1e4 0x2049fcc38c97fe3c 0xb81fee3ce1fff3e7 0xd703fdc79c3ffe7c

def z495 : W := mkw 0x0b0a180286140a10 0x8161430050c28142 0xcf0c10071e181c7f 0x39e18200e3c3038f

def z496 : W := mkw 0x0f9a1922a6160ad0 0x81f3432454c2c15a 0xfffe1ffffe1e1fff 0xffffc3ffffc3c3ff

def z497 : W := mkw 0x106586cd1be99f2f 0x420cb0d9a37d33e5 0xf8ed97c71ff99fff 0xbf1db2f8e3ff33ff

def z498 : W := mkw 0x159019280a600b01 0x02b20325014c0160 0xd71018381e601f86 0x7ae2030703cc03f0

def z499 : W := mkw 0x0b0a9e06a6969af4 0x816153c0d4d2d35e 0xff0f9e07ff9f9fff 0xffe1f3c0fff3f3ff

def z500 : W := mkw 0x0000000000000000 0x0000000000000000 0x1012600000666000 0x42024c00000ccc00

def z501 : W := mkw 0x1b0a1b6aa6b61fd7 0x8361436d54d6c3fa 0xff0e1ffffe1e1fff 0x7fe1c3ffffc3c3ff

def z502 : W := mkw 0x1db01b683ff61fd7 0x83b6036d07fec3fa 0xfff01ff81ffe1ffe 0xfffe03ff03ffc3ff

def z503 : W := mkw 0x26dfe5b540000000 0x04dbfcb6a8000000 0xa7ffe7f800000001 0xf4fffcff00000000

def z504 : W := mkw 0x0f9a5802ae564ad0 0x81f34b0055cac95a 0xdf1e7807fe7e7fff 0x7be3cf00ffcfcfff

def z505 : W := mkw 0x04d5400000000000 0x009aa80000000000 0x00f1e00000000000 0x801e3c0000000000

def z506 : W := mkw 0x04f5400019494000 0x009ea80003292800 0x98f3e00001e7e005 0xd31e7c00003cfc00

def z507 : W := mkw 0x25d5fdb540000000 0x04babfb6a8000000 0xe7f1fff800000002 0xfcfe3fff00000000

def z508 : W := mkw 0x06ff40c11d5d440a 0x40dfe81823aba881 0xdffff1c31fffec1d 0xfbfffe3863fffd83

def z509 : W := mkw 0x0000221860a2b1e4 0x200004430c14563c 0x18126838e1e7f3e4 0x43024d071c3cfe7c

def z510 : W := mkw 0x2b0abdb7e6160ad0 0x856157b6fcc2c15a 0xff0e1ffffe1e1fff 0x7fe1c3ffffc3c3ff

def z511 : W := mkw 0x24f5e7f55189942e 0x449ebcfeaa313285 0xe8fdf7ff11999c7f 0xbd1fbeffe233338f

def z512 : W := mkw 0x0065a6dd71abb5ee 0x600cb4dbae3576bd 0xe8ed9ffff1999fff 0xbd1db3fffe3333ff

def z513 : W := mkw 0x0b0a381ae6362bd0 0xa16147035cc6c57a 0x17126838ee666380 0x42e24d071dcccc70

def z514 : W := mkw 0x224fe497e002a0e0 0x2449fc92fc00541c 0x080fe007e007e061 0x0101fc00fc00fc0c

def z515 : W := mkw 0x0b2a1a42b7961ed6 0x8165434856f2c3da 0xffee1fc7ff9e1fff 0xfffdc3f8fff3c3ff

def z516 : W := mkw 0x0065024011891406 0x000ca04802312280 0xe8ed97c011999c07 0xbd1db2f802333380

def z517 : W := mkw 0x11201a481be01f07 0x02240349037c03e0 0xd70018001fe01f86 0x7ae0030003fc03f0

def z518 : W := mkw 0x030abc16c0000000 0x00615782d8000000 0xe71ffe3fe0000003 0xfce3ffc7fc000000

def z519 : W := mkw 0x15b019281b600b01 0x02b60325036c0160 0x97f008381fe00384 0xf2fe010703fc0070

def z520 : W := mkw 0x020a0000241600c0 0x004140000482c018 0x9f0e0804fe1e13e7 0x73e1c1009fc3c27c

def z521 : W := mkw 0x2145bdb7c0000000 0x0428b7b6f8000000 0xe0ed9fffe0000003 0xbc1db3fffc000000

def z522 : W := mkw 0x1490012808600101 0x02920025010c0020 0x0010003800600000 0x00020007000c0000

def z523 : W := mkw 0x00000000200200c0 0x0000000004004018 0x9813e804e1e7f3e7 0xd3027d009c3cfe7c

def z524 : W := mkw 0x15b01b683be21fc7 0x02b6036d077c43f8 0xfff21ffcffe61fe7 0xfffe43ff9ffcc3fc

def z525 : W := mkw 0x0000000000000000 0x0000000000000000 0x080c000700180079 0x01018000e003000f

def z526 : W := mkw 0x2fdf59a386140a10 0x85fbeb3470c28142 0x47ec11c31e180c18 0x28fd823863c30183

def z527 : W := mkw 0x0490400008404000 0x0092080001080800 0x0010600000606000 0x00020c00000c0c00

def z528 : W := mkw 0x0045848500098028 0x4008b090a0013005 0x0001800000018000 0x0000300000003000

def z529 : W := mkw 0x37dfffffc2a01f07 0x06fbfffff85403e0 0xe7ffffffe0001f83 0xfcfffffffc0003f0

def z530 : W := mkw 0x006586c51dddd42e 0x400cb0d8a3bbba85 0xf8ed97c71ffffc7f 0xbf1db2f8e3ffff8f

def z531 : W := mkw 0x0b6f18c3b71f0eda 0xc16de31876e3e1db 0xdfee19c7fe1e1fff 0x7bfdc338ffc3c3ff

def z532 : W := mkw 0x37fffffffbe2bfe7 0x26ffffffff7c57fc 0xffffffffffe7ffe7 0xfffffffffffcfffc

def z533 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x08ffe00001ffe001 0x811ffc00003ffc00

def z534 : W := mkw 0x05f59fe51189942e 0x40beb3fca2313285 0xeffd9fff11999c7f 0xfdffb3ffe233338f

def z535 : W := mkw 0x15b019601b400e03 0x02b6032c036801c0 0xd7f011c01fe00c04 0xfafe023803fc0180

def z536 : W := mkw 0x04b0000019400000 0x0096000003280000 0x07e000001e000000 0x20fc000003c00000

def z537 : W := mkw 0x06ffe4145d5d4000 0x00dffc828baba800 0xbfffee3cffffe007 0xf7fffdc79ffffc00

def z538 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0x57021807ee061ffa 0x4ae04300fdc0c3ff

def z539 : W := mkw 0x04f5400019494000 0x009ea80003292800 0x88fde00011f9e005 0xb11fbc00023f3c00

def z540 : W := mkw 0x0000020820a2b1e4 0x200000410414563c 0x98020804e1e7f3e7 0x530041009c3cfe7c

def z541 : W := mkw 0x0100180002000a00 0x0020030000400140 0x470010001e000c00 0x28e0020003c00180

def z542 : W := mkw 0x07ff59201d5d4000 0x00ffeb2403aba800 0xfffffff81fffe007 0xffffffff03fffc00

def z543 : W := mkw 0x0020a65c71abb5ee 0x600414cb8e3576bd 0xb813ee3cf1ffffff 0xd7027dc79e3fffff

def z544 : W := mkw 0x0000201840202100 0x2000040308040420 0x0010603800606000 0x00020c07000c0c00

def z545 : W := mkw 0x27dfffbfe0a2b1e4 0x24fbfff7fc14563c 0xe7ffffffe00013e3 0xfcfffffffc00027c

def z546 : W := mkw 0x27fffff7ddddd42e 0x44fffffefbbbba85 0xfffffffffffffc7f 0xffffffffffffff8f

def z547 : W := mkw 0x0800000006140a10 0x8100000000c28142 0x000000001e180c18 0x0000000003c30183

def z548 : W := mkw 0x002002401189942e 0x4004004802313285 0xc80c100711999c7f 0x39018200e233338f

def z549 : W := mkw 0x1020024819e01507 0x02040049033c02a0 0x0000000001e00000 0x00000000003c0000

def z550 : W := mkw 0x002000401109040a 0x4004000802212081 0x0000000010180c18 0x0000000002030183

def z551 : W := mkw 0x0000a6146082b0e4 0x200014c28c10561c 0xa803e604e187f067 0x95007cc09c30fe0c

def z552 : W := mkw 0x06dfe61c60a2b1e4 0x20dbfcc38c14563c 0xbfffee3ce1e7f3e7 0xf7fffdc79c3cfe7c

def z553 : W := mkw 0x0800020826b6bbf4 0xa100004104d6d77e 0x180000001ffffffc 0x0300000003ffffff

def z554 : W := mkw 0x0000a61c40a0b124 0x200014c388141624 0xa811e63c01e1f067 0x95023cc7803c3e0c

def z555 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0x2803ee3ce007f3e3 0x05007dc79c00fe7c

def z556 : W := mkw 0x0a0aa416e416a0f0 0xa1415482dc82d41e 0x080fe007e01fe079 0x0101fc00fc03fc0f

def z557 : W := mkw 0x06ffe6dd7dfff5ee 0x60dffcdbafbffebd 0xffffffffffffffff 0xffffffffffffffff

def z558 : W := mkw 0x06ff60187d7f61c0 0x20dfec030fafec38 0x9fffe838ffffe385 0xf3fffd071ffffc70

def z559 : W := mkw 0x0b0a1a0aa6b61bd4 0x8161434154d6c37a 0xff1e1e3ffffe1fff 0xffe3c3c7ffffc3ff

def z560 : W := mkw 0x15b09fed1be09f2f 0x42b613fda37c13e5 0xf7f01fff1fe01ffe 0xfefe03ffe3fc03ff

def z561 : W := mkw 0x069a400000000000 0x00d3480000000000 0x0712600000000000 0x40e24c0000000000

def z562 : W := mkw 0x026f86c5159d942e 0x404df0d8a2b3b285 0xffef97c71f9f9c7f 0xfffdf2f8e3f3f38f

def z563 : W := mkw 0x27df59a380000000 0x04fbeb3470000000 0xc7fff1c300000001 0xf8fffe3860000000

def z564 : W := mkw 0x11659fed13a99f2f 0x422cb3fda27533e5 0xe8ed9fff11999fff 0xbd1db3ffe23333ff

def z565 : W := mkw 0x06ff400011090000 0x00dfe80002212000 0x8fffe00011998005 0xf1fffc0002333000

def z566 : W := mkw 0x0000000800200100 0x0000000100040020 0x1010083800600380 0x42020107000c0070

def z567 : W := mkw 0x006500c11109040a 0x400ca01822212081 0xc8ed91c311998c1d 0xb91db23862333183

def z568 : W := mkw 0x15f59fe51bc99e2f 0x42beb3fca37933c5 0xefed97c71f999c7f 0xbdfdb2f8e3f3338f

def z569 : W := mkw 0x27df7932c0000000 0x04fbef2658000000 0x87ffe838e0000001 0xf0fffd071c000000

def z570 : W := mkw 0x15f519e11b490e0b 0x42bea33c236921c1 0x47ec11c31e180c18 0x28fd823863c30183

def z571 : W := mkw 0x00000000200200c0 0x0000000004004018 0xd80e1807f01e1fff 0x7b01c300fe03c3ff

def z572 : W := mkw 0x0000a4144000a020 0x2000148288001404 0x0001e0000001e000 0x00003c0000003c00

def z573 : W := mkw 0x0b0abc16e6160ad0 0x81615782dcc2c15a 0xff1ffe3ffe1e1fff 0xffe3ffc7ffc3c3ff

def z574 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0xa8ed87c011998005 0xb51db0f802333000

def z575 : W := mkw 0x01659ec513899e2e 0x402cb3d8a27133c5 0xffed9fc71f999fff 0xfffdb3f8e3f333ff

def z576 : W := mkw 0x3100bfffc2a01f07 0x062017fff85403e0 0x60001fffe0001f82 0x0c0003fffc0003f0

def z577 : W := mkw 0x002086441189942e 0x400410c882313285 0xa801860411999c7f 0x950030c08233338f

def z578 : W := mkw 0x27df79b3c0000000 0x04fbef3678000000 0x47fe79fbe0000000 0x68ffcf3f7c000000

def z579 : W := mkw 0x00008604208290e4 0x000010c08410521c 0xb8038e04e18793e7 0xd70071c09c30f27c

def z580 : W := mkw 0x0b0a180286140a10 0x8161430050c28142 0xc70e1807fe180c1b 0x78e1c300ffc30183

def z581 : W := mkw 0x1fff9fefbfff9fff 0xc3fff3fdf7fff3ff 0xffff9fffffff9fff 0xfffff3fffffff3ff

def z582 : W := mkw 0x1fba1b6abff61fd7 0x83f7436d57fec3fa 0xf7f21ff8ffe61f86 0xfefe43ff1ffcc3f0

def z583 : W := mkw 0x0000860c00a09124 0x000010c180141224 0xb8118e3c01e193e7 0xd70231c7803c327c

def z584 : W := mkw 0x04b0000019400000 0x0096000003280000 0x00f0000001e00000 0x801e0000003c0000

def z585 : W := mkw 0x04b0a61c79e2b1e4 0x209614c38f3c563c 0xbff3ee3cffe7f3e7 0xf7fe7dc79ffcfe7c

def z586 : W := mkw 0x179a59280e744b01 0x02f34b2501ce8960 0x171268380e666380 0x42e24d0701cccc70

def z587 : W := mkw 0x0100be1c62a2bbe4 0x202017c38c54577c 0xff13fe3cffe7ffe7 0xffe27fc79ffcfffc

def z588 : W := mkw 0x17ff5b681ffd5f07 0x02ffeb6d03ffabe0 0xf7fc1ff81ff81f86 0xfeff83ff03ff03f0

def z589 : W := mkw 0x27fffdb7dd5d4000 0x04ffffb6fbaba800 0xe7fffffffe180003 0xfcffffffffc30000

def z590 : W := mkw 0x0000a41440000000 0x0000148288000000 0x2011e63800000000 0x84023cc700000000

def z591 : W := mkw 0x102002481be01f07 0x02040049037c03e0 0xb0100e381fe01f86 0xd60201c703fc03f0

def z592 : W := mkw 0x0000000000000000 0x0000000000000000 0x970000001e000004 0x72e0000003c00000

def z593 : W := mkw 0x2165bff7d189942e 0x442cb7fefa313285 0xe8ed9ffff1999c7f 0xbd1db3fffe33338f

def z594 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x17fe60001e7e6000 0x62ffcc0003cfcc00

def z595 : W := mkw 0x100000080a600b01 0x02000001014c0160 0x100000000e600380 0x0200000001cc0070

def z596 : W := mkw 0x0020024811a01506 0x00040049023402a0 0xf0f01ff811e01f86 0xfe1e03ff023c03f0

def z597 : W := mkw 0x1fff5b6abfff5fd7 0x83ffeb6d57ffebfa 0xffffffffffffffff 0xffffffffffffffff

def z598 : W := mkw 0x14b002481be01f07 0x02960049037c03e0 0x97f000001fe01f84 0xf2fe000003fc03f0

def z599 : W := mkw 0x15b09f6c1be09f27 0x02b613ed837c13e4 0xfff19ffc1fe19fe7 0xfffe33ff83fc33fc

def z600 : W := mkw 0x2ffffdb7ff5f4ad0 0x85ffffb6ffebe95a 0xffffffffffffffff 0xffffffffffffffff

def z601 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0x28ed87c701998079 0x851db0f8e033300f

def z602 : W := mkw 0x06df400004140000 0x00dbe80000828000 0x9fffe0001e1e0005 0xf3fffc0003c3c000

def z603 : W := mkw 0x0045a69d60abb1ec 0x6008b4d3ac15763d 0xb81fee3fe1fff3ff 0xd703fdc7fc3ffe7f

def z604 : W := mkw 0x17ba1b681ff41f07 0x02f7436d03fe83e0 0xfffe1ff81ffe1f87 0xffffc3ff03ffc3f0

def z605 : W := mkw 0x09001802a6160ad0 0x8120030054c2c15a 0x58001807fe1e1ffe 0x0b000300ffc3c3ff

def z606 : W := mkw 0x27ff59a39d5d4000 0x04ffeb3473aba800 0xdffff1c31fffe005 0xfbfffe3863fffc00

def z607 : W := mkw 0x0000a41440000000 0x0000148288000000 0x0003e004e0000001 0x00007c009c000000

def z608 : W := mkw 0x0045008100090008 0x4008a01020012001 0x000c000300180018 0x0001800060030003

def z609 : W := mkw 0x37ba7b7adbe01f07 0x06f74f6f5b7c03e0 0xf7f27ff8ffe01f86 0xfefe4fff1ffc03f0

def z610 : W := mkw 0x04f5400019494000 0x009ea80003292800 0x97f1e0001fe1e004 0xf2fe3c0003fc3c00

def z611 : W := mkw 0x2000a497c0000000 0x04001492f8000000 0x00000007e0000000 0x00000000fc000000

def z612 : W := mkw 0x2b4ffc97e6160ad0 0x8569ff92fcc2c15a 0xdf0ff807fe1e1fff 0x7be1ff00ffc3c3ff

def z613 : W := mkw 0x06ff42401dddd42e 0x40dfe84803bbba85 0x9fffe0001ffffc7d 0xf3fffc0003ffff8f

def z614 : W := mkw 0x069a40000c544000 0x00d34800018a8800 0x9f1e60001e7e6005 0x73e3cc0003cfcc00

def z615 : W := mkw 0x14b0a77c79e2b5e7 0x229614ef8f3c56bc 0xb8f3effce1e7f3e7 0xd71e7dff9c3cfe7c

def z616 : W := mkw 0x0b0a9ec7a6969efe 0xc16153d8f4d2d3df 0xff0e1fc7fe1e1fff 0x7fe1c3f8ffc3c3ff

def z617 : W := mkw 0x17ff5b681be01f07 0x02ffeb6d037c03e0 0xf7fffff81fe01f87 0xfeffffff03fc03f0

def z618 : W := mkw 0x06df4000041d4000 0x00dbe8000083a800 0x8fffe000001fe001 0xf1fffc000003fc00

def z619 : W := mkw 0x17ffff7c7fffffe7 0x22ffffef8ffffffc 0xfffffffcffffffe7 0xffffffff9ffffffc

def z620 : W := mkw 0x06ba40001d544000 0x00d7480003aa8800 0x97f260001fe66004 0xf2fe4c0003fccc00

def z621 : W := mkw 0x14b0036819e01507 0x0296006d033c02a0 0xb7f007f81fe00004 0xf6fe00ff03fc0000

def z622 : W := mkw 0x04b0024019c01406 0x0096004803380280 0xf7f017c01fe01c06 0xfefe02f803fc0380

def z623 : W := mkw 0x004586850089902c 0x4008b0d0a0113205 0xa80d86070199907f 0x9501b0c0e033320f

def z624 : W := mkw 0x086586c5379f9efe 0xc10cb0d8a6f3f3df 0xf8ed97c71f9f9fff 0xbf1db2f8e3f3f3ff

def z625 : W := mkw 0x0000a4146002a0e0 0x200014828c00541c 0x9813e004e1e7e065 0xd3027c009c3cfc0c

def z626 : W := mkw 0x0000020000801004 0x0000004000100200 0xa000060001801006 0x940000c000300200

def z627 : W := mkw 0x0000020800a01104 0x0000004100140220 0x20000e3800001382 0x040001c700000270

def z628 : W := mkw 0x27ff59e39109040a 0x44ffeb3c72212081 0x47ec11c310180c18 0x28fd823862030183

def z629 : W := mkw 0x06df40000c544000 0x00dbe800018a8800 0x97ffe0000e666001 0xf2fffc0001cccc00

def z630 : W := mkw 0x0a0a0002a41600d0 0x814140005482c01a 0x980e0807e01e13ff 0x5301c100fc03c27f

def z631 : W := mkw 0x1100192802200b01 0x0220032500440160 0x0000083800000380 0x0000010700000070

def z632 : W := mkw 0x0590192000000000 0x00b2032400000000 0x0710083800000000 0x40e2010700000000

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0x8801800001818005 0x9100300000303000

def z634 : W := mkw 0x279afd36c0000000 0x04f35fa6d8000000 0xa713ee3ce0000003 0xd4e27dc79c000000

def z635 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0x480e1807e01e1ffb 0x0901c300fc03c3ff

def z636 : W := mkw 0x15b01b681ffd5f07 0x02b6036d03ffabe0 0xfff01ff81fffff86 0xfffe03ff03fffff0

def z637 : W := mkw 0x27dffdb7e002a0e0 0x24fbffb6fc00541c 0xefffffffe007e063 0xfdfffffffc00fc0c

def z638 : W := mkw 0x279afdb7c0000000 0x04f35fb6f8000000 0x67127fffe0000002 0x4ce24ffffc000000

def z639 : W := mkw 0x1100196002000e03 0x0220032c004001c0 0x400011c000000c00 0x0800023800000180

def z640 : W := mkw 0x15f59fed1be99f2f 0x42beb3fda37d33e5 0xf7f19ff81fe19f86 0xfefe33ff03fc33f0

def z641 : W := mkw 0x0900be1ee2a2bbf4 0xa12017c3dc54577e 0xf813fe3fe1e7ffff 0xdf027fc7fc3cffff

def z642 : W := mkw 0x06ffe4147d5fe0e0 0x20dffc828fabfc1c 0x9fffe004ffffe065 0xf3fffc009ffffc0c

def z643 : W := mkw 0x14b0036819e01507 0x0296006d033c02a0 0xe0f017f811e01c06 0xbc1e02ff023c0380

def z644 : W := mkw 0x06ba00001d540000 0x00d7400003aa8000 0x9ffe00001ffe0005 0xf3ffc00003ffc000

def z645 : W := mkw 0x27fffffff1abb5ee 0x64fffffffe3576bd 0xfffffffff1ffffff 0xfffffffffe3fffff

def z646 : W := mkw 0x0490000000000000 0x0092000000000000 0x87f0000000000000 0xf0fe000000000000

def z647 : W := mkw 0x0065000011090000 0x000ca00002212000 0x00ec000010180000 0x201d800002030000

def z648 : W := mkw 0x04f5e61c59e9f124 0x209ebcc38b3d3e24 0x20f1e63801e1e000 0x841e3cc7003c3c00

def z649 : W := mkw 0x0045000000000000 0x0008a00000000000 0x80ed800000000001 0xb01db00000000000

def z650 : W := mkw 0x0fffdec7bfdfdefe 0xc1fffbd8f7fbfbdf 0xffffffc7ffffffff 0xfffffff8ffffffff

def z651 : W := mkw 0x24d5e5b540000000 0x049abcb6a8000000 0xe0fdf7ff00000003 0xbc1fbeffe0000000

def z652 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0xe0e197c011819c06 0xbc1c32f802303380

def z653 : W := mkw 0x024f4000041d4000 0x0049e8000083a800 0x981fe00001ffe005 0xd303fc00003ffc00

def z654 : W := mkw 0x0065000011090000 0x000ca00002212000 0x00e1800001818000 0x801c300000303000

def z655 : W := mkw 0x020a000004140000 0x0041400000828000 0x170200000e060000 0x42e0400001c0c000

def z656 : W := mkw 0x0020a65c71a2b5e6 0x200414cb8e3456bc 0xf8f3fffcf1e7ffe7 0xff1e7fff9e3cfffc

def z657 : W := mkw 0x0000020820a2b1e4 0x200000410414563c 0xb8100e3801e7f3e6 0xd70201c7003cfe7c

def z658 : W := mkw 0x27dffdbfe02221c0 0x24fbffb7fc044438 0xf7ffffffe0666383 0xfefffffffc0ccc70

def z659 : W := mkw 0x27fffdb7d1090000 0x04ffffb6fa212000 0xeffffffff1998007 0xfdfffffffe333000

def z660 : W := mkw 0x15f55b681be95f07 0x02beab6d037d2be0 0xf7f1fff81fe1ff86 0xfefe3fff03fc3ff0

def z661 : W := mkw 0x0fdf5802a6160ad0 0x81fbeb0054c2c15a 0xdffff807fe1e1fff 0xfbffff00ffc3c3ff

def z662 : W := mkw 0x0000a4146002a0e0 0x200014828c00541c 0x9803e804e007f3e7 0x53007d009c00fe7c

def z663 : W := mkw 0x27dfdda780000000 0x04fbfbb4f0000000 0xe7ed97c700000003 0xbcfdb2f8e0000000

def z664 : W := mkw 0x2f9a7932e6160ad0 0x85f34f265cc2c15a 0xdf1e783ffe1e1fff 0x7be3cf07ffc3c3ff

def z665 : W := mkw 0x37ff59e39b400e03 0x06ffeb3c736801c0 0x47ec11c31e000c00 0x28fd823863c00180

def z666 : W := mkw 0x27dfffb7c0809024 0x04fbfff6f8101204 0xefffffffe1819067 0xfdfffffffc30320c

def z667 : W := mkw 0x0800000026160ad0 0x8100000004c2c15a 0x100000000e060380 0x0200000001c0c070

def z668 : W := mkw 0x06ff42401ddd5406 0x00dfe84803bbaa80 0xfffff7c01ffffc07 0xfffffef803ffff80

def z669 : W := mkw 0x0020004011000402 0x0004000802200080 0x40e011c010000c00 0x281c023802000180

def z670 : W := mkw 0x002002401dddd42e 0x4004004803bbba85 0x180000001ffffc7c 0x0300000003ffff8f

def z671 : W := mkw 0x0100180002000a00 0x0020030000400140 0x170008000e000380 0x42e0010001c00070

def z672 : W := mkw 0x0b4f9c87a61f8af8 0xc169f390f4c3f15f 0xdf0f9807fe1f9fff 0x7be1f300ffc3f3ff

def z673 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0x080d800711999c7d 0x0101b000e233338f

def z674 : W := mkw 0x0065a6dd51a9b52e 0x600cb4dbaa3536a5 0x20f1e7f801e1e000 0x841e3cff003c3c00

def z675 : W := mkw 0x14f587ed19e9952f 0x429eb0fda33d32a5 0x20f187f801e18000 0x841e30ff003c3000

def z676 : W := mkw 0x0065860411899024 0x000cb0c082313204 0xa8ed860411999067 0xb51db0c08233320c

def z677 : W := mkw 0x0065a6d5718bb4ee 0x600cb4daae31769d 0xe8eff7c7f19ffc7f 0xbd1dfef8fe33ff8f

def z678 : W := mkw 0x030a180280000000 0x0061430050000000 0xcf0e1807f0181c7f 0x79e1c300fe03038f

def z679 : W := mkw 0x006500001d5d4000 0x000ca00003aba800 0x98ed80001fffe005 0xb31db00003fffc00

def z680 : W := mkw 0x06ffe61c5dfdf124 0x20dffcc38bbfbe24 0xbfffe6381fffe005 0xf7fffcc703fffc00

def z681 : W := mkw 0x0045a495600ba0e8 0x6008b492ac01741d 0x080fe007e01fe079 0x0101fc00fc03fc0f

def z682 : W := mkw 0x006500c11109040a 0x400ca01822212081 0x00e001c000000000 0x001c003800000000

def z683 : W := mkw 0x020a000004140000 0x0041400000828000 0x070c00001e180000 0x20e1800003c30000

def z684 : W := mkw 0x159039386a622bc1 0x22b207270d4c4578 0x17126838ee666380 0x42e24d071dcccc70

def z685 : W := mkw 0x0fff58029f5d4a10 0x81ffeb0053eba942 0x47ec10031e180c18 0x28fd820063c30183

def z686 : W := mkw 0x000086c50080942e 0x400010d8a0101285 0xe80c17c710181c7f 0x3d0182f8e203038f

def z687 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0xb0100e3ce1e013e6 0xd60201c79c3c027c

def z688 : W := mkw 0x0b4f9c87a6160ad0 0x8169f390f4c2c15a 0xffef9fc7fe1e1fff 0xfffdf3f8ffc3c3ff

def z689 : W := mkw 0x0eff4002bd5f40d0 0x81dfe80057abe81a 0x9fffe007ffffe07d 0xf3fffc00fffffc0f

def z690 : W := mkw 0x27dfffbfc0a01104 0x04fbfff7f8140220 0xf7ffffffe1e01387 0xfefffffffc3c0270

def z691 : W := mkw 0x224fe497c0000000 0x0449fc92f8000000 0xa01fee3fe0000003 0xd403fdc7fc000000

def z692 : W := mkw 0x004586c50080942e 0x4008b0d8a0101285 0xe0ed97c700001c7b 0xbc1db2f8e000038f

def z693 : W := mkw 0x0020864411809426 0x000410c882301284 0xe8e197c411819c67 0xbd1c32f88230338c

def z694 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0x60e197c701819c7a 0x8c1c32f8e030338f

def z695 : W := mkw 0x27fffdb7d9494000 0x04ffffb6fb292800 0xe7ffffffe1e1e003 0xfcfffffffc3c3c00

def z696 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0x28e187c011999c7c 0x851c30f80233338f

def z697 : W := mkw 0x05901b2800a01104 0x00b2036500140220 0xf7f01ff801e01386 0xfefe03ff003c0270

def z698 : W := mkw 0x00002010600220c0 0x200004020c004418 0x00026000e0066000 0x00004c001c00cc00

def z699 : W := mkw 0x026f40001d5d4000 0x004de80003aba800 0x180fe0001fffe005 0x0301fc0003fffc00

def z700 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0xd70e1807ee060383 0x7ae1c300fdc0c070

def z701 : W := mkw 0x06dfe41440000000 0x00dbfc8288000000 0xa7ffee3ce0000003 0xf4fffdc79c000000

def z702 : W := mkw 0x0045848500098028 0x4008b090a0013005 0xc80d900710199c7f 0x3901b200e203338f

def z703 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0x9f020804ee0613e7 0x53e041009dc0c27c

def z704 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0xa8e187c401819067 0x951c30f88030320c

def z705 : W := mkw 0x06dfc48500000000 0x00dbf890a0000000 0xe7fff7c700000003 0xfcfffef8e0000000

def z706 : W := mkw 0x0000020820a211c4 0x0000004104144238 0xb8120e3ce1e613e7 0xd70241c79c3cc27c

def z707 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0x67fe7fffe0000002 0x6cffcffffc000000

def z708 : W := mkw 0x0000a69d60a2b1ec 0x600014d3ac14563d 0xb813ee3fe1e7f3ff 0xd7027dc7fc3cfe7f

def z709 : W := mkw 0x069a40000c544000 0x00d34800018a8800 0x9f1fe0001fffe005 0xf3e3fc0003fffc00

def z710 : W := mkw 0x06ffe61c7dfff1e4 0x20dffcc38fbffe3c 0x27ec0e3cfe1813e2 0x24fd81c79fc3027c

def z711 : W := mkw 0x15b01b681be09f2f 0x42b6036d037c13e5 0xf7f01ff81fe01ffe 0xfefe03ff03fc03ff

def z712 : W := mkw 0x134f5b6806bd5f07 0x0269eb6d00d7abe0 0x680ffff8001fff83 0x0d01ffff0003fff0

def z713 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xe7ed9fffe0000003 0xbcfdb3fffc000000

def z714 : W := mkw 0x06ff400019400000 0x00dfe80003280000 0x9fffe0001fe7e005 0xf3fffc0003fcfc00

def z715 : W := mkw 0x27df7932c0000000 0x04fbef2658000000 0xe7fffff8e0000003 0xfcffffff1c000000

def z716 : W := mkw 0x279a7932c0000000 0x04f34f2658000000 0x27f26ff8e0000000 0xc4fe4dff1c000000

def z717 : W := mkw 0x0b0abe1ec6b4bb34 0xa16157c3d8d69766 0x671df63b1ff9ec18 0xace3bec763ff3d83

def z718 : W := mkw 0x24d5e5b7c0000000 0x049abcb6f8000000 0x20f1e7ffe0000000 0x841e3cfffc000000

def z719 : W := mkw 0x1eba036abdf615d7 0x83d7406d57bec2ba 0x28fe07ffe1fe0079 0x851fc0fffc3fc00f

def z720 : W := mkw 0x15b01b681be99f2f 0x42b6036d037d33e5 0xfffc1fff1ff99fff 0xffff83ffe3ff33ff

def z721 : W := mkw 0x2a4fe497e416a0f0 0xa549fc92fc82d41e 0x080fe007e01fe079 0x0101fc00fc03fc0f

def z722 : W := mkw 0x15b05b681be05f07 0x02b60b6d037c0be0 0xf7f07ff81fe07f86 0xfefe0fff03fc0ff0

def z723 : W := mkw 0x0065848511090000 0x000cb090a2212000 0xe8ed97c711999c7f 0xbd1db2f8e233338f

def z724 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xf7f3fff81fe01f87 0xfefe7fff03fc03f0

def z725 : W := mkw 0x2fdffdb7c6140a10 0x85fbffb6f8c28142 0xf7fffffffe181f9f 0xfeffffffffc303f3

def z726 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xf7fc1ffb1ff81f9e 0xfeff83ff63ff03f3

def z727 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xe7f01ff81e001f82 0xfcfe03ff03c003f0

def z728 : W := mkw 0x27dffdb7c2000a00 0x04fbffb6f8400140 0xf7ffffffee000383 0xfefffffffdc00070

def z729 : W := mkw 0x2100bdb7c0000000 0x042017b6f8000000 0xe0e01fffe0000002 0xbc1c03fffc000000

def z730 : W := mkw 0x25d5fdb7c0000000 0x04babfb6f8000000 0xe7f1ffffe0000002 0xfcfe3ffffc000000

def z731 : W := mkw 0x15b01b681be99f2f 0x42b6036d037d33e5 0xf7f01ff81fe19f86 0xfefe03ff03fc33f0

def z732 : W := mkw 0x0b0a1922a6160ad0 0x8161432454c2c15a 0xff0e1ffffe1e1fff 0x7fe1c3ffffc3c3ff

def z733 : W := mkw 0x006500c11109842a 0x400ca01822213085 0x48ec11c310198c78 0x291d82386203318f

def z734 : W := mkw 0x2145bdb7c0000000 0x0428b7b6f8000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z735 : W := mkw 0x0b6f9ec7b79f9efe 0xc16df3d8f6f3f3df 0x37e38fc0ef878380 0xc6fc71f81df0f070

def z736 : W := mkw 0x15b01b681be95f07 0x02b6036d037d2be0 0xf7f01ff81fe1ff86 0xfefe03ff03fc3ff0

def z737 : W := mkw 0x2cd5e5b566160ad0 0x859abcb6acc2c15a 0x38f1e7f81e1e1ffc 0x871e3cff03c3c3ff

def z738 : W := mkw 0x15901b6802a01f07 0x02b2036d005403e0 0xf7f01ff81e001f86 0xfefe03ff03c003f0

def z739 : W := mkw 0x006586c519c9942e 0x400cb0d8a3393285 0xf8ed97c71ff99c7f 0xbf1db2f8e3ff338f

def z740 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0xdf0ff807fe1fffff 0x7be1ff00ffc3ffff

def z741 : W := mkw 0x27dffdb7c000a020 0x24fbffb6f8001404 0xe7ffffffe001e003 0xfcfffffffc003c00

def z742 : W := mkw 0x06ff40811d5d4000 0x00dfe81023aba800 0xdffff1c31fffe005 0xfbfffe3863fffc00

def z743 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0xe8fdf7c711f9fc7f 0xbd1fbef8e23f3f8f

def z744 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0xe8fff7c711999c7f 0xfd1ffef8e233338f

def z745 : W := mkw 0x006520d9712b25ca 0x600ca41b2e2564b9 0x50fe79fbf07e6f98 0x6a1fcf3f7e0fcdf3

def z746 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0xe8eff7c7119ffc7f 0xbd1dfef8e233ff8f

def z747 : W := mkw 0x006500c11109040a 0x400ca01822212081 0x40ec11c710181c7a 0x281d8238e203038f

def z748 : W := mkw 0x06ba40001d5d4000 0x00d7480003aba800 0x9f13e0001fffe005 0xd3e27c0003fffc00

def z749 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xfff21ff81fe61f87 0xfffe43ff03fcc3f0

def z750 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0xf81ffe3fe1e7f3e7 0xff03ffc7fc3cfe7c

def z751 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x9fffe0041ffff067 0xf3fffc0083fffe0c

def z752 : W := mkw 0x15d59dad0a698b29 0x42bab3b5a14d3165 0x1f1d883f0e7983f9 0x43e3b107e1cf307f

def z753 : W := mkw 0x27ba7b72d189942e 0x44f74f6e5a313285 0x0f126838f1999c7c 0x41e24d071e33338f

def z754 : W := mkw 0x006586c519c9d42e 0x400cb0d8a3393a85 0xe8ed97c711f9fc7f 0xbd1db2f8e23f3f8f

def z755 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0xcf0c1807fe181fff 0x39e18300ffc303ff

def z756 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xe7fc1fffe0000002 0xfcff83fffc000000

def z757 : W := mkw 0x106586cd19e9952f 0x420cb0d9a33d32a5 0xe8ed97c711f99c7f 0xbd1db2f8e23f338f

def z758 : W := mkw 0x326fe6dfdbe01f07 0x064dfcdbfb7c03e0 0x100fe007ffe01f85 0x0201fc00fffc03f0

def z759 : W := mkw 0x182002483ff6bff7 0xa304004907fed7fe 0x180000001ffffffc 0x0300000003ffffff

def z760 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0xbf13ee3cffe7f3e7 0xf7e27dc79ffcfe7c

def z761 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xf7fffffffe000007 0xfeffffffffc00000

def z762 : W := mkw 0x1fff59629f5d4e13 0x83ffeb2c53eba9c2 0x47ec11c31e180c18 0x28fd823863c30183

def z763 : W := mkw 0x006586cd11a9b52e 0x600cb0d9a23536a5 0xe8ed97c711f9fc7f 0xbd1db2f8e23f3f8f

def z764 : W := mkw 0x2120bdb7dd5d4000 0x042417b6fbaba800 0x78001fffffffe006 0x0f0003fffffffc00

def z765 : W := mkw 0x26ff40839d5d4000 0x04dfe81073aba800 0x9fffe0031fffe005 0xf3fffc0063fffc00

def z766 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xefffffffe1818007 0xfdfffffffc303000

def z767 : W := mkw 0x26dfe5b7c0000000 0x04dbfcb6f8000000 0xe0fff7ffe0000003 0xbc1ffefffc000000

def z768 : W := mkw 0x0045848500098028 0x4008b090a0013005 0xe8ed97c710199c7f 0xbd1db2f8e203338f

def z769 : W := mkw 0x0900be1ee2a2bbf4 0xa12017c3dc54577e 0x20000e3ce00013e2 0x040001c79c00027c

def z770 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0xe8ef9fc7f1999c7f 0xfd1df3f8fe33338f

def z771 : W := mkw 0x06df40000c5d4000 0x00dbe800018ba800 0x9f1fe0000fffe005 0xd3e3fc0001fffc00

def z772 : W := mkw 0x27dffdb7c4140000 0x04fbffb6f8828000 0xfffffffffe1e1c7f 0xffffffffffc3c38f

def z773 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0xdffff0071fffe007 0xfbfffe00e3fffc00

def z774 : W := mkw 0x25d5fdb7c0000000 0x04babfb6f8000000 0xe0f3ffffe0000003 0xdc1e7ffffc000000

def z775 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0x570e1807fe1e1ffa 0x6ae1c300ffc3c3ff

def z776 : W := mkw 0x006584c51109842a 0x400cb098a2213085 0xc8ed91c710199c7f 0x391db238e203338f

def z777 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0xf8ef97c7119f9c7f 0xff1df2f8e233f38f

def z778 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0xf8ed97c711fffc7f 0xbf1db2f8e23fff8f

def z779 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xf7ffffffe0666003 0xfefffffffc0ccc00

def z780 : W := mkw 0x15b0bd747b42aee3 0x22b617ae8f6855dc 0x4fe3f1c4fe07ec61 0x29fc7e389fc0fd8c

def z781 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xefffffffe018007b 0xfdfffffffc03000f

def z782 : W := mkw 0x24d5e5b540000000 0x049abcb6a8000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z783 : W := mkw 0x0065a6d55189942e 0x400cb4daaa313285 0xe8eff7c7f1999c7f 0xbd1dfef8fe33338f

def z784 : W := mkw 0x0d90192026160ad0 0x81b2032404c2c15a 0xfff01ff81e1e1ffe 0xfffe03ff03c3c3ff

def z785 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0x68ec17c711999c7e 0x2d1d82f8e233338f

def z786 : W := mkw 0x27dffdb7c8400000 0x04fbffb6f9080000 0xf7ffffffee600003 0xfefffffffdcc0000

def z787 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xe7fffffff0180c1b 0xfcfffffffe030183

def z788 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0xdf1ff807fe1e1fff 0xfbe3ff00ffc3c3ff

def z789 : W := mkw 0x07df9da780000000 0x00fbf3b4f0000000 0xe7ff9fffe0000003 0xfcfff3fffc000000

def z790 : W := mkw 0x0590192002000a00 0x00b2032400400140 0xf7f01ff80e000382 0xfefe03ff01c00070

def z791 : W := mkw 0x05b019201b400a00 0x00b6032403680140 0xf7f01ff81fe01f86 0xfefe03ff03fc03f0

def z792 : W := mkw 0x37ff59e39f5d4e03 0x06ffeb3c73eba9c0 0x47ec11c31e180c00 0x28fd823863c30180

def z793 : W := mkw 0x14b003681be01f07 0x0296006d037c03e0 0xb7f007f81fe01f84 0xf6fe00ff03fc03f0

def z794 : W := mkw 0x06ff40811d5d4008 0x40dfe81023aba801 0x9fffe0031fffe01d 0xf3fffc0063fffc03

def z795 : W := mkw 0x27dffdb7c0008020 0x04fbffb6f8001004 0xefffffffe0018063 0xfdfffffffc00300c

def z796 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0xe8ec17c710181c7f 0x3d1d82f8e203038f

def z797 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0x48ed91c711999c7d 0x291db238e233338f

def z798 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x97f3e0001fe7e004 0xf2fe7c0003fcfc00

def z799 : W := mkw 0x2590bdb7c0000000 0x04b217b6f8000000 0x67e01fffe0000002 0x2cfc03fffc000000

def z800 : W := mkw 0x15b01b681be91f07 0x02b6036d037d23e0 0xfff01ff81ff99f86 0xfffe03ff03ff33f0

def z801 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8ec17c710181c7f 0xbd1d82f8e203038f

def z802 : W := mkw 0x0df55802bb4b4ad0 0x81beab005769695a 0x40f1f807e1e1fffa 0x881e3f00fc3c3fff

def z803 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x17ffe0001fffe000 0xe2fffc0003fffc00

def z804 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xe7ee1fffe0000003 0x7cfdc3fffc000000

def z805 : W := mkw 0x2145bdb7c0000000 0x0428b7b6f8000000 0x60e19fffe0000002 0x8c1c33fffc000000

def z806 : W := mkw 0x0590192280000000 0x00b2032450000000 0xe7f01fffe0000002 0xfcfe03fffc000000

def z807 : W := mkw 0x26ff41a11d5d4000 0x04dfe83423aba800 0x9fffe1c01fffe005 0xf3fffc3803fffc00

def z808 : W := mkw 0x06ff40c11d5d440a 0x40dfe81823aba881 0xdffff1c71ffffc7f 0xfbfffe38e3ffff8f

def z809 : W := mkw 0x2a4fe497e41600d0 0x8549fc92fc82c01a 0x000fe007e0060001 0x0001fc00fc00c000

def z810 : W := mkw 0x024fe495641fe0e8 0x6049fc92ac83fc1d 0x080fe007e01fe079 0x0101fc00fc03fc0f

def z811 : W := mkw 0x27dffdb7c4140000 0x04fbffb6f8828000 0xffffffffffffe007 0xfffffffffffffc00

def z812 : W := mkw 0x2fdffdb7c6140a10 0x85fbffb6f8c28142 0xfffffffffe1e0c1f 0xffffffffffc3c183

def z813 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xf7fc1fff1fe01f87 0xfeff83ffe3fc03f0

def z814 : W := mkw 0x2f9a5922a6160ad0 0x85f34b2454c2c15a 0x17020800ee060380 0x42e041001dc0c070

def z815 : W := mkw 0x0065c6c51189d42e 0x400cb8d8a2313a85 0xe8edf7c71199fc7f 0xbd1dbef8e2333f8f

def z816 : W := mkw 0x0a4fa497e41fa0f8 0xe149f492fc83f41f 0x080fe007e01fe079 0x0101fc00fc03fc0f

def z817 : W := mkw 0x0590192000000000 0x00b2032400000000 0xe7f21ffce0000003 0xfcfe43ff9c000000

def z818 : W := mkw 0x05b01b2819e01104 0x00b60365033c0220 0xf7f01ff81fe01386 0xfefe03ff03fc0270

def z819 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0x2813ee3ce1e7f3e3 0x85027dc79c3cfe7c

def z820 : W := mkw 0x00002018602221c0 0x200004030c044438 0x9813e83ce1e7f3e7 0xd3027d079c3cfe7c

def z821 : W := mkw 0x006584c51109842a 0x400cb098a2213085 0x40ec11c710180c78 0x281d8238e203018f

def z822 : W := mkw 0x2900bfbfe2a2bbf4 0xa52017f7fc54577e 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z823 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0x27ffefffe0000001 0xc4fffdfffc000000

def z824 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0x68ed97c311999c7c 0xad1db2f86233338f

def z825 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xf7f01fff1fe01ffe 0xfefe03ffe3fc03ff

def z826 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x1ff3e0001fffe004 0xc3fe7c0003fffc00

def z827 : W := mkw 0x27dffdb7c4140000 0x04fbffb6f8828000 0xf7ffffffee060003 0xfefffffffdc0c000

def z828 : W := mkw 0x27dffdb7c0098028 0x44fbffb6f8013005 0xeffffffff0199c7f 0xfdfffffffe03338f

def z829 : W := mkw 0x182002483ff61fd7 0x8304004907fec3fa 0x100000001fe61f84 0x0200000003fcc3f0

def z830 : W := mkw 0x0065a6d55189942e 0x400cb4daaa313285 0xe8fdf7ff11999c7f 0xbd1fbeffe233338f

def z831 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0xbfffee381fffe007 0xf7fffdc703fffc00

def z832 : W := mkw 0x25903932c0000000 0x04b2072658000000 0xe7f01ff8e0000002 0xfcfe03ff1c000000

def z833 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xa7ffeff8e0000001 0xf4fffdff1c000000

def z834 : W := mkw 0x0000221860a231c4 0x200004430c144638 0xb813ee38e1e7f387 0xd7027dc71c3cfe70

def z835 : W := mkw 0x026f0000151d0000 0x004de00002a3a000 0x9fffe0001fffe005 0xf3fffc0003fffc00

def z836 : W := mkw 0x05d5bdb540000000 0x00bab7b6a8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z837 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xf7ffffffe1e00007 0xfefffffffc3c0000

def z838 : W := mkw 0x15b01b681be09f27 0x02b6036d037c13e4 0xfff01ff81fe19fe6 0xfffe03ff03fc33fc

def z839 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xf7f21ffcffe01f87 0xfefe43ff9ffc03f0

def z840 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x1fefe0001fffe005 0x23fdfc0003fffc00

def z841 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xb7f00ff81fe00384 0xf6fe01ff03fc0070

def z842 : W := mkw 0x25d5bdb7c0000000 0x04bab7b6f8000000 0xe7fd9fffe0000003 0xfcffb3fffc000000

def z843 : W := mkw 0x26dfe5b540000000 0x04dbfcb6a8000000 0xa7ffeffce0000003 0xf4fffdff9c000000

def z844 : W := mkw 0x04f5400019494000 0x009ea80003292800 0x9ff3e0001fe7e005 0xf3fe7c0003fcfc00

def z845 : W := mkw 0x0000a61c40a01104 0x000014c388140220 0xb813ee3ce1e7f387 0xd7027dc79c3cfe70

def z846 : W := mkw 0x069ac6c50cd4d42e 0x40d358d8a19a9a85 0x771277c70e667c7a 0x4ee24ef8e1cccf8f

def z847 : W := mkw 0x06ba40001d544000 0x00d7480003aa8800 0x9ff3e0001fe7e005 0xf3fe7c0003fcfc00

def z848 : W := mkw 0x006584c51109842a 0x400cb098a2213085 0xe8ed97c710198c7b 0xbd1db2f8e203318f

def z849 : W := mkw 0x27df5baba0a2b1e4 0x24fbeb757414563c 0x5fec11c301e7f3e4 0x2bfd8238603cfe7c

def z850 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0x67fffffbe0000000 0xecffffff7c000000

def z851 : W := mkw 0x0000a41440000000 0x0000148288000000 0xe0f3fffce0000003 0xfc1e7fff9c000000

def z852 : W := mkw 0x0065a6dd51a9b52e 0x600cb4dbaa3536a5 0xe8ed97ff11999c7f 0xbd1db2ffe233338f

def z853 : W := mkw 0x25d5fdb7c0000000 0x04babfb6f8000000 0xe0fdffffe0000003 0xbc1fbffffc000000

def z854 : W := mkw 0x020a000004140000 0x0041400000828000 0x9f13e0000fe7e005 0xd3e27c0001fcfc00

def z855 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0x77f01ff81fe00f80 0xeefe03ff03fc01f0

def z856 : W := mkw 0x0000a65c60a2b5ee 0x600014cb8c1456bd 0xb813ee3ce1e7ffff 0xd7027dc79c3cffff

def z857 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0xffee1fc7fe1e1fff 0xfffdc3f8ffc3c3ff

def z858 : W := mkw 0x00002018602221c0 0x200004030c044438 0x1013e838e1e7e380 0xc2027d071c3cfc70

def z859 : W := mkw 0x24d5e5b540000000 0x049abcb6a8000000 0x20f3eff8e0000000 0xc41e7dff1c000000

def z860 : W := mkw 0x0065a6d55189942e 0x400cb4daaa313285 0xe8ed9ffff1999c7f 0xbd1db3fffe33338f

def z861 : W := mkw 0x0065a6dd51a9b52e 0x600cb4dbaa3536a5 0xe8fffffff1f9fc7f 0xfd1ffffffe3f3f8f

def z862 : W := mkw 0x15b01b681be0bf27 0x22b6036d037c17e4 0xf7f01ff81fe1ff86 0xfefe03ff03fc3ff0

def z863 : W := mkw 0x0020004011000402 0x0004000802200080 0xc8ec11c710181c7f 0x391d8238e203038f

def z864 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xfffc1ff81ff81f87 0xffff83ff03ff03f0

def z865 : W := mkw 0x27dffdb7cc5d4000 0x04fbffb6f98ba800 0xffffffffee7fe003 0xfffffffffdcffc00

def z866 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0x67f01ff81fe01f82 0xacfe03ff03fc03f0

def z867 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0x68ed97c711998c79 0xad1db2f8e233318f

def z868 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xf7ffffffe0001387 0xfefffffffc000270

def z869 : W := mkw 0x0065a6dd51a9b52e 0x600cb4dbaa3536a5 0xf8fff7ff11fffc7f 0xff1ffeffe23fff8f

def z870 : W := mkw 0x006502c11189942e 0x400ca05822313285 0x40ec11c310181c78 0x281d82386203038f

def z871 : W := mkw 0x06df40000c544000 0x00dbe800018a8800 0x9fffe0000fe7e005 0xf3fffc0001fcfc00

def z872 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0xb81fee3cf1fff3e7 0xf703fdc79e3ffe7c

def z873 : W := mkw 0x27dffdb7c41dc028 0x44fbffb6f883b805 0xefffffffe01fe07b 0xfdfffffffc03fc0f

def z874 : W := mkw 0x27df79b3c0000000 0x04fbef3678000000 0xe7fe7ffbe0000002 0xfcffcfff7c000000

def z875 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0xb81fee3fe1fff3ff 0xd703fdc7fc3ffe7f

def z876 : W := mkw 0x279afdb7c0000000 0x04f35fb6f8000000 0xe7f27fffe0000002 0xfcfe4ffffc000000

def z877 : W := mkw 0x2a4fe497e41f80f8 0xc549fc92fc83f01f 0x080fe007e01f8079 0x0101fc00fc03f00f

def z878 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0xf8fd97c711f99c7f 0xff1fb2f8e23f338f

def z879 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0xf813fe3cf1e7ffe7 0xff027fc79e3cfffc

def z880 : W := mkw 0x006586cd11a9952e 0x400cb0d9a23532a5 0xf8ed97c711f99fff 0xbf1db2f8e23f33ff

def z881 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0xf813fe3fe1e7ffff 0xdf027fc7fc3cffff

def z882 : W := mkw 0x09001802a2020ad0 0x812003005440415a 0xdf0c1807fe181fff 0x7be18300ffc303ff

def z883 : W := mkw 0x14b0036819e01507 0x0296006d033c02a0 0xb7f00ff81fe01386 0xf6fe01ff03fc0270

def z884 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0x5f0c1807fe1e1ffe 0x2be18300ffc3c3ff

def z885 : W := mkw 0x279abdb7c0000000 0x04f357b6f8000000 0xe7fe1fffe0000003 0xfcffc3fffc000000

def z886 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xf7f1fff81fe1ff86 0xfefe3fff03fc3ff0

def z887 : W := mkw 0x05901b2802a01b04 0x00b2036500540360 0xf7f01ff81fe01f86 0xfefe03ff03fc03f0

def z888 : W := mkw 0x0065a6d55189942e 0x400cb4daaa313285 0xf8fffffff1fffc7f 0xff1ffffffe3fff8f

def z889 : W := mkw 0x0000a6dd60a2b5ee 0x600014dbac1456bd 0xb813effce1e7f3e7 0xd7027dff9c3cfe7c

def z890 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xfff01ff81ff81ffe 0xfffe03ff03ff03ff

def z891 : W := mkw 0x2f9a793ae6362bd0 0xa5f34f275cc6c57a 0x17126838ee666380 0x42e24d071dcccc70

def z892 : W := mkw 0x06df400004140000 0x00dbe80000828000 0x9fffe0001fffe005 0xf3fffc0003fffc00

def z893 : W := mkw 0x06ff41201d5d4000 0x00dfe82403aba800 0xbfffe7f81fffe005 0xf7fffcff03fffc00

def z894 : W := mkw 0x27dffdb7c0098028 0x44fbffb6f8013005 0xe7ffffffe0018003 0xfcfffffffc003000

def z895 : W := mkw 0x006586c511801406 0x000cb0d8a2300280 0xe8ed97c711981c7f 0xbd1db2f8e233038f

def z896 : W := mkw 0x0f9a1922a6160ad0 0x81f3432454c2c15a 0x17120838ee060380 0x42e241071dc0c070

def z897 : W := mkw 0x1900bf7ee2a2bff7 0xa32017efdc5457fe 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z898 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0x37f00ff81fe01f84 0xc6fe01ff03fc03f0

def z899 : W := mkw 0x0065a6dd51a9b52e 0x600cb4dbaa3536a5 0xf8fdffff11f9ffff 0xff1fbfffe23f3fff

def z900 : W := mkw 0x1db01b6a9be01f17 0x83b6036d537c03e2 0xf7f01ffb1fe01f9e 0xfefe03ff63fc03f3

def z901 : W := mkw 0x026f40001d5d4000 0x004de80003aba800 0x9f0fe0001fffe005 0x73e1fc0003fffc00

def z902 : W := mkw 0x04f5e6dd59e9f52e 0x609ebcdbab3d3ea5 0x20f1e7f801e1e000 0x841e3cff003c3c00

def z903 : W := mkw 0x006586cd11a9952e 0x400cb0d9a23532a5 0xe8fd97ff11f99c7f 0xbd1fb2ffe23f338f

def z904 : W := mkw 0x1f9a1922ae560ad1 0x83f3432455cac15a 0x17020800ee060380 0x42e041001dc0c070

def z905 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xfff01ff81fe7ff86 0xfffe03ff03fcfff0

def z906 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0xf8ed9fc711999fff 0xff1db3f8e23333ff

def z907 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x1f1fe0001fffe005 0x43e3fc0003fffc00

def z908 : W := mkw 0x182002483be21fd7 0x83040049077c43fa 0x100000001fe01ffc 0x0200000003fc03ff

def z909 : W := mkw 0x06dfe49540000000 0x00dbfc92a8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z910 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xe7ffffffe0001c7b 0xfcfffffffc00038f

def z911 : W := mkw 0x0000a69d60a2b1e4 0x200014d3ac14563c 0xf813ffffe1e7f3e7 0xdf027ffffc3cfe7c

def z912 : W := mkw 0x15b019281b600b01 0x02b60325036c0160 0xf7f01ff81fe00386 0xfefe03ff03fc0070

def z913 : W := mkw 0x159019280a600b01 0x02b20325014c0160 0x37f00ff80e600380 0xc6fe01ff01cc0070

def z914 : W := mkw 0x27dffdb7c2000a00 0x04fbffb6f8400140 0xe7fffffffe000c03 0xfcffffffffc00180

def z915 : W := mkw 0x0820024837bfbffe 0xe104004906f7f7ff 0x180000001ffffffc 0x0300000003ffffff

def z916 : W := mkw 0x224fe497e41fe0e0 0x2449fc92fc83fc1c 0x080fe007e01fe061 0x0101fc00fc03fc0c

def z917 : W := mkw 0x27dffdb7c4140000 0x04fbffb6f8828000 0xe7fffffffe180003 0xfcffffffffc30000

def z918 : W := mkw 0x27dffdb7cc544000 0x04fbffb6f98a8800 0xfffffffffe7e6007 0xffffffffffcfcc00

def z919 : W := mkw 0x0000a41c6022a1e0 0x200014838c04543c 0x9813e83ce1e7e3e5 0xd3027d079c3cfc7c

def z920 : W := mkw 0x002002483dfff5ee 0x6004004907bffebd 0x180000001ffffffc 0x0300000003ffffff

def z921 : W := mkw 0x04f5000019490000 0x009ea00003292000 0x9fffe0001fffe005 0xf3fffc0003fffc00

def z922 : W := mkw 0x2065e6d55189942e 0x440cbcdaaa313285 0xe8edf7c711999c7f 0xbd1dbef8e233338f

def z923 : W := mkw 0x26dfe5b7c0000000 0x04dbfcb6f8000000 0xa7ffe7ffe0000001 0xf4fffcfffc000000

def z924 : W := mkw 0x102002483bebbfef 0x62040049077d77fd 0x180000001ffffffc 0x0300000003ffffff

def z925 : W := mkw 0x15b019601b400e03 0x02b6032c036801c0 0xf7f01ff81e001f86 0xfefe03ff03c003f0

def z926 : W := mkw 0x27dffdb7c41d4000 0x04fbffb6f883a800 0xffffffffe1ffe007 0xfffffffffc3ffc00

def z927 : W := mkw 0x06ba00001d540000 0x00d7400003aa8000 0x9fffe0001fffe005 0xf3fffc0003fffc00

def z928 : W := mkw 0x069a40000c544000 0x00d34800018a8800 0x1713e0000fe7e000 0xc2e27c0001fcfc00

def z929 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0x68ed97c701999c7b 0x8d1db2f8e033338f

def z930 : W := mkw 0x024f4000041d4000 0x0049e8000083a800 0x9f1fe0001fffe005 0xf3e3fc0003fffc00

def z931 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0xe8fd9fff11999c7f 0xfd1fb3ffe233338f

def z932 : W := mkw 0x1020024839e2b5e7 0x22040049073c56bc 0x1800000001e7f3e4 0x03000000003cfe7c

def z933 : W := mkw 0x006586cd11a9952e 0x400cb0d9a23532a5 0xe8ed9fff11999fff 0xbd1db3ffe23333ff

def z934 : W := mkw 0x26dfe5b7c0000000 0x04dbfcb6f8000000 0xa0ffefffe0000003 0xd41ffdfffc000000

def z935 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0xb813ee38e1e7e385 0xd7027dc71c3cfc70

def z936 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xe7e01ff81f801f86 0xbcfc03ff03f003f0

def z937 : W := mkw 0x279a7932c0000000 0x04f34f2658000000 0xe7fe7fffe0000003 0xfcffcffffc000000

def z938 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x9fffe8001ffff387 0xf3fffd0003fffe70

def z939 : W := mkw 0x07dffd3440000000 0x00fbffa688000000 0xe7fffffce0000003 0xfcffffff9c000000

def z940 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0x77f017f81fe01f84 0xaefe02ff03fc03f0

def z941 : W := mkw 0x0490000008400000 0x0092000001080000 0x9f13e0000fe7e005 0xd3e27c0001fcfc00

def z942 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xa7f3effce0000003 0xd4fe7dff9c000000

def z943 : W := mkw 0x004586c50080942e 0x4008b0d8a0101285 0xe8ed97c710181c7f 0xbd1db2f8e203038f

def z944 : W := mkw 0x006584c51109842a 0x400cb098a2213085 0xc8ed91c711998c7d 0xb91db238e233318f

def z945 : W := mkw 0x0020024831a2b5e6 0x20040049063456bc 0x1800000011e7ffe4 0x03000000023cfffc

def z946 : W := mkw 0x0100be1c62a2bbe4 0x202017c38c54577c 0x60001e3ce0001fe2 0x0c0003c79c0003fc

def z947 : W := mkw 0x27dffdb7c41d4000 0x04fbffb6f883a800 0xfffffffffe1fe007 0xffffffffffc3fc00

def z948 : W := mkw 0x2fdffdb7c2000a10 0x85fbffb6f8400142 0xe7ffffffe0000c1b 0xfcfffffffc000183

def z949 : W := mkw 0x102002483fffffe7 0x2204004907fffffc 0x180000001fffffe4 0x0300000003fffffc

def z950 : W := mkw 0x15b019681b600f03 0x02b6032d036c01e0 0xf7f01ff81e600f82 0xfefe03ff03cc01f0

def z951 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0x1813e83ce1e7f3e5 0x43027d079c3cfe7c

def z952 : W := mkw 0x2fdffdb7c4140010 0x85fbffb6f8828002 0xe7ffffffe018001b 0xfcfffffffc030003

def z953 : W := mkw 0x3f9a793aee760bd1 0x87f34f275dcec17a 0x17126838ee660380 0x42e24d071dccc070

def z954 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0x4f0e1807fe1e1ffb 0x29e1c300ffc3c3ff

def z955 : W := mkw 0x030a180282000a00 0x0061430050400140 0xdf0e1807fe181fff 0x7be1c300ffc303ff

def z956 : W := mkw 0x0065024011891406 0x000ca04802312280 0xe8ed97c711999c7f 0xbd1db2f8e233338f

def z957 : W := mkw 0x006586cd11a9952e 0x400cb0d9a23532a5 0xf8ffffff11ffffff 0xff1fffffe23fffff

def z958 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xf7f27ff81fe67f86 0xfefe4fff03fccff0

def z959 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0x67f3ffffe0000002 0xccfe7ffffc000000

def z960 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xffffffffe0060007 0xfffffffffc00c000

def z961 : W := mkw 0x26dfe5b7c0000000 0x04dbfcb6f8000000 0x20f3e7f8e0000000 0x841e7cff1c000000

def z962 : W := mkw 0x0490a53440000000 0x009214a688000000 0xa0f3effce0000003 0xd41e7dff9c000000

def z963 : W := mkw 0x0045868500809024 0x0008b0d0a0101204 0xe8ed97c711999c7f 0xbd1db2f8e233338f

def z964 : W := mkw 0x2a4fe497e41f40d0 0x8549fc92fc83e81a 0x080fe007e01fe079 0x0101fc00fc03fc0f

def z965 : W := mkw 0x25d5fdb7c0000000 0x04babfb6f8000000 0x60e01fffe0000002 0x0c1c03fffc000000

def z966 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0x67fff7ffe0000001 0xacfffefffc000000

def z967 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xe7f3fff8e0000002 0xfcfe7fff1c000000

def z968 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0x1f0e0807fe1e1ffd 0x43e1c100ffc3c3ff

def z969 : W := mkw 0x15901b280ae01b05 0x02b20365015c0360 0xf7f01ff80fe01386 0xfefe03ff01fc0270

def z970 : W := mkw 0x2145bdb7c0000000 0x0428b7b6f8000000 0x60ec1fffe0000002 0x2c1d83fffc000000

def z971 : W := mkw 0x006500c11109040a 0x400ca01822212081 0xc8ed91c711999c7f 0xb91db238e233338f

def z972 : W := mkw 0x2590bdb7c0000000 0x04b217b6f8000000 0xe7f3ffffe0000003 0xfcfe7ffffc000000

def z973 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xfff01ffc1fe01fe7 0xfffe03ff83fc03fc

def z974 : W := mkw 0x0100180022020ac0 0x0020030004404158 0xdf0e1807fe1e1fff 0x7be1c300ffc3c3ff

def z975 : W := mkw 0x1100bffd62a2bfef 0x622017ffac5457fd 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z976 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0xdf0e1807ffffffff 0x7be1c300ffffffff

def z977 : W := mkw 0x27dffdb7c0094000 0x04fbffb6f8012800 0xe7ffffffe001e003 0xfcfffffffc003c00

def z978 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xfff19ff81fe19f87 0xfffe33ff03fc33f0

def z979 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0xd70c1807fe181ffe 0x7ae18300ffc303ff

def z980 : W := mkw 0x16ff41601d5d4403 0x02dfe82c03aba880 0x9fffe1c01fffe005 0xf3fffc3803fffc00

def z981 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0xff1e1e3ffe1e1fff 0xffe3c3c7ffc3c3ff

def z982 : W := mkw 0x102002483be21fc7 0x02040049077c43f8 0x180000001fe61fe4 0x0300000003fcc3fc

def z983 : W := mkw 0x27dffdb7c41d4000 0x04fbffb6f883a800 0xe7ffffffe0180003 0xfcfffffffc030000

def z984 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x9fffe804ffffe007 0xf3fffd009ffffc00

def z985 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x97ffe0000fe7e001 0xf2fffc0001fcfc00

def z986 : W := mkw 0x034fbc97c0000000 0x0069f792f8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z987 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0xdffff0031fffec1d 0xfbfffe0063fffd83

def z988 : W := mkw 0x006502c11189140e 0x400ca05822312281 0xe8ec17c711981c7f 0xbd1d82f8e233038f

def z989 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0x3813ee38e1e7f3e4 0xc7027dc71c3cfe7c

def z990 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0x60ed97c711999c7a 0xac1db2f8e233338f

def z991 : W := mkw 0x27dffdb7c0090008 0x44fbffb6f8012001 0xe7ffffffe018001b 0xfcfffffffc030003

def z992 : W := mkw 0x27dffdb7c0090000 0x04fbffb6f8012000 0xefffffffe0198003 0xfdfffffffc033000

def z993 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xe7ffffffe1e1e003 0xfcfffffffc3c3c00

def z994 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0xb013ee38e1e7f386 0xd6027dc71c3cfe70

def z995 : W := mkw 0x0a0a0002a6160ad0 0x8141400054c2c15a 0x9f0e0007fe1e1ffd 0x73e1c000ffc3c3ff

def z996 : W := mkw 0x14f5a7fd59e9b52f 0x629eb4ffab3d36a5 0x20f1e7f801e1e000 0x841e3cff003c3c00

def z997 : W := mkw 0x0065a6dd51a9952e 0x400cb4dbaa3532a5 0xf8fffffff1f99fff 0xff1ffffffe3f33ff

def z998 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0xe0ed97c710181c7b 0xbc1db2f8e203038f

def z999 : W := mkw 0x27dffdb7c6140a00 0x04fbffb6f8c28140 0xfffffffffe1e1f87 0xffffffffffc3c3f0

def z1000 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0x77f01ff81e601f82 0x6efe03ff03cc03f0

def z1001 : W := mkw 0x0000020820a211c4 0x0000004104144238 0xb813ee3ce1e7f3e7 0xd7027dc79c3cfe7c

def z1002 : W := mkw 0x234fbdb7c0000000 0x0469f7b6f8000000 0xe7ef9fffe0000003 0xfcfdf3fffc000000

def z1003 : W := mkw 0x0000a414600200c0 0x000014828c004018 0xb813ee3ce1e7f3e7 0xd7027dc79c3cfe7c

def z1004 : W := mkw 0x2fff59a39f5d4a10 0x85ffeb3473eba942 0x47ec11c31e180c18 0x28fd823863c30183

def z1005 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0x68ed97c710199c7b 0x2d1db2f8e203338f

def z1006 : W := mkw 0x020a0000241600c0 0x004140000482c018 0xdf0e1807fe1e1fff 0x7be1c300ffc3c3ff

def z1007 : W := mkw 0x06ff40401d5d4402 0x00dfe80803aba880 0xdffff1c01fffec05 0xfbfffe3803fffd80

def z1008 : W := mkw 0x159019280a600b01 0x02b20325014c0160 0xf7f01ff81e601f86 0xfefe03ff03cc03f0

def z1009 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0xdf1e7807fe7e7fff 0x7be3cf00ffcfcfff

def z1010 : W := mkw 0x2fdffdb7c6140a10 0x85fbffb6f8c28142 0xeffffffffe181c7f 0xfdffffffffc3038f

def z1011 : W := mkw 0x102002483be23fc7 0x22040049077c47f8 0x100000001fe67f84 0x0200000003fccff0

def z1012 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0xfffff7c01fffe007 0xfffffef803fffc00

def z1013 : W := mkw 0x37dffdb7ca400a01 0x06fbffb6f9480140 0xe7ffffffee000003 0xfcfffffffdc00000

def z1014 : W := mkw 0x0020864411809426 0x000410c882301284 0xe8ed97c711999c7f 0xbd1db2f8e233338f

def z1015 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xf7f01ff80fe00382 0xfefe03ff01fc0070

def z1016 : W := mkw 0x01201a4813a01f06 0x00240349027403e0 0xf7f01ff81fe01f86 0xfefe03ff03fc03f0

def z1017 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x9ff3e0000fe7e005 0xd3fe7c0001fcfc00

def z1018 : W := mkw 0x1f9a592aae764bd1 0x83f34b2555cec97a 0x17126838ee666380 0x42e24d071dcccc70

def z1019 : W := mkw 0x11201b6813a01f07 0x0224036d027403e0 0xf7e01ff81f801f86 0xfefc03ff03f003f0

def z1020 : W := mkw 0x234ffdb7c0000000 0x0469ffb6f8000000 0xe0efffffe0000003 0xbc1dfffffc000000

def z1021 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0xb813ee3cf1ffffff 0xd7027dc79e3fffff

def z1022 : W := mkw 0x06ff40029d5d4000 0x00dfe80053aba800 0x9fffe007ffffe005 0xf3fffc00fffffc00

def z1023 : W := mkw 0x3100bfffe2a2bfe7 0x262017fffc5457fc 0x60001fffe0001fe2 0x0c0003fffc0003fc

def z1024 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x1fffe0000fffe001 0xc3fffc0001fffc00

def z1025 : W := mkw 0x182002483fff9fff 0xc304004907fff3ff 0x180000001fff9ffc 0x0300000003fff3ff

def z1026 : W := mkw 0x04b0024819e01506 0x00960049033c02a0 0xf7f01ff81fe01f86 0xfefe03ff03fc03f0

def z1027 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x0fffe0001fffe001 0xa1fffc0003fffc00

def z1028 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0xf8f3fffce1e7f3e7 0xff1e7fff9c3cfe7c

def z1029 : W := mkw 0x2f9a7932ee564ad0 0x85f34f265dcac95a 0x17126838ee666380 0x42e24d071dcccc70

def z1030 : W := mkw 0x279afd36c0000000 0x04f35fa6d8000000 0xe7f3fffce0000003 0xfcfe7fff9c000000

def z1031 : W := mkw 0x1100bf3c62a2bbe5 0x222017e78c54577c 0x20000e3ce00013e2 0x040001c79c00027c

def z1032 : W := mkw 0x079a192280000000 0x00f3432450000000 0xe7f21ff8e0000002 0xfcfe43ff1c000000

def z1033 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0xdf1e1807fffe1fff 0xfbe3c300ffffc3ff

def z1034 : W := mkw 0x0590393040000000 0x00b2072608000000 0xe7f27ff8e0000002 0xfcfe4fff1c000000

def z1035 : W := mkw 0x27dffdb7c2000a00 0x04fbffb6f8400140 0xe7ffffffe0001f83 0xfcfffffffc0003f0

def z1036 : W := mkw 0x006500c11109040a 0x400ca01822212081 0x48ec11c710180c79 0x291d8238e203018f

def z1037 : W := mkw 0x04f540001d5d4000 0x009ea80003aba800 0x9ff1e0001fffe004 0xf3fe3c0003fffc00

def z1038 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0x67fdffffe0000002 0xacffbffffc000000

def z1039 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xeffffffff0180007 0xfdfffffffe030000

def z1040 : W := mkw 0x224fe497c0000000 0x0449fc92f8000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z1041 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0xc70e1807fe181ffb 0x78e1c300ffc303ff

def z1042 : W := mkw 0x25d5fdb7c0000000 0x04babfb6f8000000 0x20f1eff8e0000000 0x841e3dff1c000000

def z1043 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x9fffe0071fffe07d 0xf3fffc00e3fffc0f

def z1044 : W := mkw 0x34f5e7fd59e9952f 0x469ebcffab3d32a5 0x20f1e7f801e18000 0x841e3cff003c3000

def z1045 : W := mkw 0x002086c51180942e 0x400410d8a2301285 0xe8ec17c711981c7f 0xbd1d82f8e233038f

def z1046 : W := mkw 0x15b01b6a9be01f07 0x02b6036d537c03e0 0xf7f01fffffe01f86 0xfefe03fffffc03f0

def z1047 : W := mkw 0x27dffdb7cc544000 0x04fbffb6f98a8800 0xffffffffefe7e007 0xfffffffffdfcfc00

def z1048 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xb7f00ff80fe01386 0xd6fe01ff01fc0270

def z1049 : W := mkw 0x102002483be2bfe7 0x22040049077c57fc 0x100000001fe01fe4 0x0200000003fc03fc

def z1050 : W := mkw 0x0020024831abb5ee 0x60040049063576bd 0x1800000001e7f3e4 0x03000000003cfe7c

def z1051 : W := mkw 0x0000a6dd60a2b5ee 0x600014dbac1456bd 0xf81ffffff1ffffff 0xff03fffffe3fffff

def z1052 : W := mkw 0x004586c50089942e 0x4008b0d8a0113285 0xe8ed97c700199c7b 0xbd1db2f8e003338f

def z1053 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xefffffffe0001067 0xfdfffffffc00020c

def z1054 : W := mkw 0x24d5e5b540000000 0x049abcb6a8000000 0x20f1effce0000002 0x841e3dff9c000000

def z1055 : W := mkw 0x0eff40029d5d4010 0x81dfe80053aba802 0x9fffe0031fffe01d 0xf3fffc0063fffc03

def z1056 : W := mkw 0x04b000001d5d4000 0x0096000003aba800 0x9ff3e0001fffe005 0xf3fe7c0003fffc00

def z1057 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0xdf0f9807ff9f9fff 0xfbe1f300fff3f3ff

def z1058 : W := mkw 0x27dffdb7c8404000 0x04fbffb6f9080800 0xe7ffffffe0606003 0xfcfffffffc0c0c00

def z1059 : W := mkw 0x006502c11189942e 0x400ca05822313285 0xc8ec11c711999c7f 0x391d8238e233338f

def z1060 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0x3813ee3ce1e7e3e1 0xc7027dc79c3cfc7c

def z1061 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xe7fffffff0001c07 0xfcfffffffe000380

def z1062 : W := mkw 0x06ff40401d5d440a 0x40dfe80803aba881 0x9fffe0001fffec1d 0xf3fffc0003fffd83

def z1063 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0xf7e01ff81e001f86 0x7efc03ff03c003f0

def z1064 : W := mkw 0x0b0a1802a6160ad0 0x8161430054c2c15a 0x5f0e1007fe1e1ffd 0x2be1c200ffc3c3ff

def z1065 : W := mkw 0x0000a65c60a2b5e6 0x200014cb8c1456bc 0xf813fffce1e7ffe7 0xdf027fff9c3cfffc

def z1066 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0xb013ee3ce1e7e383 0xd6027dc79c3cfc70

def z1067 : W := mkw 0x022a00001d5d4000 0x0045400003aba800 0x9f1fe0001fffe005 0xf3e3fc0003fffc00

def z1068 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x9fffe0001ffffc7d 0xf3fffc0003ffff8f

def z1069 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0x77f01ff80fe01f82 0xcefe03ff01fc03f0

def z1070 : W := mkw 0x2fdffdb7c6140a10 0x85fbffb6f8c28142 0xe7ffffffee000003 0xfcfffffffdc00000

def z1071 : W := mkw 0x0045a49540000000 0x0008b492a8000000 0xe0ed9fffe0000003 0xbc1db3fffc000000

def z1072 : W := mkw 0x27dffdb7c2000a00 0x04fbffb6f8400140 0xfffffffffe181fff 0xffffffffffc303ff

def z1073 : W := mkw 0x0000000000000000 0x0000000000000000 0x9f13e0001fe7e005 0xf3e27c0003fcfc00

def z1074 : W := mkw 0x0900bedfe2a2bffe 0xe12017dbfc5457ff 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z1075 : W := mkw 0x05b01b6013801e06 0x00b6036c027003c0 0xf7f01ff81f801f86 0xfefe03ff03f003f0

def z1076 : W := mkw 0x0000a41c602221c0 0x200014838c044438 0xb813ee3ce1e7e387 0xd7027dc79c3cfc70

def z1077 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0xe0ec17c711981c7e 0xbc1d82f8e233038f

def z1078 : W := mkw 0x15b01b681be91f0f 0x42b6036d037d23e1 0xf7f01ff81ff81f9e 0xfefe03ff03ff03f3

def z1079 : W := mkw 0x006586c51189942e 0x400cb0d8a2313285 0xffed97c71f999c7f 0xfffdb2f8e3f3338f

def z1080 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0x60ffffffe0000003 0x8c1ffffffc000000

def z1081 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0x67efffffe0000003 0x2cfdfffffc000000

def z1082 : W := mkw 0x24d5e5b540000000 0x049abcb6a8000000 0x20f3e7fce0000001 0x841e7cff9c000000

def z1083 : W := mkw 0x0020024831abb5ee 0x60040049063576bd 0x0800000011999ffc 0x01000000023333ff

def z1084 : W := mkw 0x0000221860a2b1e4 0x200004430c14563c 0x9813e838e1e7f3e5 0xd3027d071c3cfe7c

def z1085 : W := mkw 0x006502c11189942e 0x400ca05822313285 0xe8ec17c311999c7e 0xbd1d82f86233338f

def z1086 : W := mkw 0x25d5fdb540000000 0x04babfb6a8000000 0xe7f3fffce0000003 0xfcfe7fff9c000000

def z1087 : W := mkw 0x07df592280000000 0x00fbeb2450000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1088 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0x1ffde0001fffe004 0xa3ffbc0003fffc00

def z1089 : W := mkw 0x27dffdb7c0008028 0x44fbffb6f8001005 0xe7ffffffe000007b 0xfcfffffffc00000f

def z1090 : W := mkw 0x06ff40001d5d4000 0x00dfe80003aba800 0xdffff0001ffffc07 0xfbfffe0003ffff80

def z1091 : W := mkw 0x2590bdb7c0000000 0x04b217b6f8000000 0x60f01fffe0000002 0x8c1e03fffc000000

def z1092 : W := mkw 0x0065a6d55189b42e 0x600cb4daaa313685 0xe8edf7c71199fc7f 0xbd1dbef8e2333f8f

def z1093 : W := mkw 0x006500c11109040a 0x400ca01822212081 0x48ec11c310181c7c 0x291d82386203038f

def z1094 : W := mkw 0x182002483fff5fd7 0x8304004907ffebfa 0x180000001ffffffc 0x0300000003ffffff

def z1095 : W := mkw 0x15b01b681be01f07 0x02b6036d037c03e0 0x77e01ff81fe01f86 0x2efc03ff03fc03f0

def z1096 : W := mkw 0x006502c11189942e 0x400ca05822313285 0xc8ed91c311999c7d 0xb91db2386233338f

def z1097 : W := mkw 0x27dffdb7c4144000 0x04fbffb6f8828800 0xe7ffffffe0066003 0xfcfffffffc00cc00

def z1098 : W := mkw 0x002002401189942e 0x4004004802313285 0xe8ec17c711999c7f 0xbd1d82f8e233338f

def z1099 : W := mkw 0x1f9a393aee762bd1 0xa3f347275dcec57a 0x17126838ee666380 0x42e24d071dcccc70

def z1100 : W := mkw 0x079abd36c0000000 0x00f357a6d8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1101 : W := mkw 0x132a1a4a9be01f07 0x02654349537c03e0 0xd70e1807ffe01f87 0x7ae1c300fffc03f0

def z1102 : W := mkw 0x0590bd3440000000 0x00b217a688000000 0xe7f01ffce0000002 0xfcfe03ff9c000000

def z1103 : W := mkw 0x27dffdb7c0000000 0x04fbffb6f8000000 0xefffffffe007e003 0xfdfffffffc00fc00

def z1104 : W := mkw 0x0045a49540000000 0x0008b492a8000000 0xa0f3effce0000003 0xd41e7dff9c000000

def z1105 : W := mkw 0x27dffdb7cc544000 0x04fbffb6f98a8800 0xe7ffffffee000003 0xfcfffffffdc00000

def z1106 : W := mkw 0x27df59a380000000 0x04fbeb3470000000 0xe7fe1fffe0000003 0xfcffc3fffc000000

def z1107 : W := mkw 0x15901b680ae01f07 0x02b2036d015c03e0 0xf7f01ff80e601f82 0xfefe03ff01cc03f0

def z1108 : W := mkw 0x006584c51109040a 0x400cb098a2212081 0xe8ed97c710181c7f 0xbd1db2f8e203038f

def z1109 : W := mkw 0x06ff40c11d5d440a 0x40dfe81823aba881 0x9fffe1c01fffe005 0xf3fffc3803fffc00

def z1110 : W := mkw 0x0b0a5802a6164ad0 0x81614b0054c2c95a 0xdf0e7807fe1e7fff 0x7be1cf00ffc3cfff

def z1111 : W := mkw 0x27dffdb7c4140000 0x04fbffb6f8828000 0xefffffffe01e0003 0xfdfffffffc03c000

def z1112 : W := mkw 0x0045008100000000 0x0008a01020000000 0xc8ec11c710181c7f 0x391d8238e203038f

def z1113 : W := mkw 0x0000a61c60a2b1e4 0x200014c38c14563c 0x3013ee3ce1e7f3e2 0xc6027dc79c3cfe7c

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z8,z6,z9]),(0,[z1,z7,z3,z4,z5,z6,z10]),(0,[z1,z7,z3,z11,z4,z5,z6]),(0,[z1,z7,z3,z4,z12,z5,z6])],[(1,[z1,z7,z3,z13,z5,z6]),(0,[z1,z7,z3,z14,z4,z5,z6])],[(0,[z1,z7,z3,z4,z15,z5,z6]),(0,[z1,z7,z3,z4,z5,z16,z6]),(0,[z17,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z18,z5,z6]),(1,[z1,z7,z3,z4,z19,z6]),(0,[z20,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z21,z3,z4,z5,z6]),(0,[z1,z7,z22,z23,z4,z5,z6]),(0,[z1,z7,z22,z3,z12,z5,z6]),(0,[z1,z7,z3,z4,z5,z24,z6])],[(0,[z25,z7,z3,z4,z26,z5,z6]),(0,[z27,z1,z7,z28,z4,z5,z6]),(0,[z29,z1,z7,z3,z4,z30,z6]),(0,[z1,z31,z7,z3,z4,z5,z6]),(0,[z1,z32,z7,z4,z5,z33,z6])],[(0,[z34,z1,z7,z3,z4,z5,z6]),(0,[z35,z1,z7,z3,z4,z5,z6]),(0,[z1,z36,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z37,z6]),(0,[z1,z7,z38,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z39,z6]),(0,[z1,z7,z40,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z41,z6]),(0,[z1,z7,z3,z42,z4,z5,z6]),(0,[z1,z7,z3,z4,z43,z6,z44])],[(0,[z1,z7,z45,z3,z4,z5,z6]),(0,[z46,z1,z7,z3,z4,z5,z6]),(0,[z47,z1,z7,z3,z4,z48,z6]),(0,[z49,z1,z7,z3,z4,z5,z6]),(0,[z50,z1,z7,z3,z4,z5,z6]),(0,[z1,z51,z7,z3,z4,z5,z52]),(0,[z1,z7,z3,z4,z5,z6,z53]),(0,[z1,z7,z54,z3,z4,z5,z6])],[(0,[z1,z55,z7,z3,z4,z5,z6]),(0,[z1,z7,z56,z3,z4,z5,z6]),(0,[z1,z57,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z58])]],
   [[(0,[z27,z1,z7,z59,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z6]),(0,[z1,z7,z3,z4,z5,z60,z6]),(0,[z1,z7,z3,z4,z5,z6,z61]),(0,[z1,z62,z3,z59,z4,z5,z6])],[(0,[z1,z63,z7,z3,z4,z5,z6]),(0,[z0,z1,z7,z3,z4,z5,z6])],[(1,[z1,z7,z3,z4,z5,z64]),(0,[z65,z1,z7,z3,z4,z5,z6])],[(1,[z1,z7,z3,z4,z5,z66]),(0,[z47,z1,z7,z3,z4,z5,z67])],[(0,[z1,z68,z3,z59,z4,z5,z6]),(0,[z27,z1,z7,z69,z4,z5,z6]),(0,[z1,z70,z7,z3,z4,z5,z53]),(0,[z1,z7,z71,z3,z4,z5,z72]),(0,[z1,z7,z73,z3,z4,z5,z6])],[(0,[z47,z7,z3,z74,z4,z5,z6]),(0,[z1,z75,z7,z3,z4,z5,z6]),(0,[z29,z7,z3,z4,z76,z5,z6])],[(1,[z77,z7,z3,z26,z5,z6]),(0,[z1,z78,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z79,z4,z5,z6]),(0,[z80,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z81,z5,z6]),(0,[z82,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z83,z5,z6])],[(0,[z1,z7,z71,z3,z4,z5,z6]),(0,[z1,z7,z84,z3,z4,z5,z85]),(0,[z1,z7,z3,z4,z5,z86,z6])],[(0,[z1,z7,z3,z4,z5,z6,z87]),(0,[z1,z7,z88,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z89,z5,z6])],[(0,[z1,z7,z23,z3,z4,z5,z6]),(0,[z90,z1,z7,z3,z4,z91,z6]),(0,[z1,z7,z3,z4,z92,z5,z6])],[(0,[z93,z1,z7,z3,z4,z5,z6]),(0,[z94,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z95,z4,z5,z6]),(0,[z1,z7,z96,z4,z26,z5,z6]),(0,[z97,z1,z98,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z99,z6]),(0,[z1,z7,z3,z4,z5,z100,z6]),(0,[z1,z7,z3,z59,z4,z5,z6]),(0,[z90,z1,z7,z3,z101,z5,z6]),(0,[z90,z1,z3,z4,z5,z52,z6]),(0,[z1,z102,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z103,z6]),(0,[z1,z7,z3,z4,z5,z104,z6])],[(0,[z105,z1,z7,z3,z4,z5,z6]),(0,[z1,z106,z3,z107,z4,z5,z6]),(0,[z108,z1,z7,z3,z4,z5,z6]),(0,[z109,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z110,z5,z6]),(0,[z97,z1,z7,z3,z4,z76,z6])],[(0,[z1,z7,z3,z4,z5,z111,z6]),(0,[z1,z7,z112,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z113,z6]),(0,[z77,z1,z7,z3,z26,z5,z6]),(0,[z1,z7,z114,z3,z4,z5,z6]),(0,[z1,z7,z3,z115,z4,z5,z6])],[(0,[z1,z7,z3,z4,z116,z5,z30]),(0,[z1,z117,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z115,z118,z5,z6]),(0,[z1,z7,z3,z4,z5,z119,z6])],[(0,[z120,z1,z7,z3,z4,z5,z6]),(0,[z1,z68,z3,z107,z4,z5,z6]),(0,[z47,z27,z7,z3,z4,z5,z6]),(0,[z121,z1,z7,z3,z4,z5,z6]),(0,[z27,z1,z7,z23,z4,z5,z6]),(0,[z1,z122,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z123,z6]),(0,[z124,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z69,z4,z5,z6]),(0,[z1,z7,z125,z3,z4,z5,z6]),(0,[z1,z7,z3,z126,z5,z127,z6])],[(0,[z1,z7,z3,z4,z5,z128,z6]),(0,[z1,z7,z3,z4,z5,z129,z6]),(0,[z1,z7,z3,z130,z4,z5,z6])],[(0,[z131,z1,z7,z3,z4,z5,z6]),(0,[z97,z7,z3,z4,z5,z30,z6]),(0,[z1,z7,z3,z4,z132,z5,z6]),(0,[z1,z117,z3,z107,z4,z5,z6]),(0,[z1,z3,z4,z5,z52,z6,z53]),(0,[z1,z70,z7,z3,z4,z133,z6]),(1,[z1,z32,z7,z4,z5,z33]),(0,[z1,z7,z71,z3,z115,z5,z6])],[(0,[z1,z7,z134,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z135])],[(0,[z1,z7,z3,z4,z5,z6,z136]),(0,[z1,z7,z137,z3,z4,z5,z6]),(0,[z1,z7,z138,z4,z5,z6,z139])],[(0,[z1,z7,z140,z3,z4,z5,z6]),(0,[z1,z7,z28,z3,z4,z141,z6]),(0,[z1,z7,z3,z4,z142,z5,z6])]],
   [[(0,[z1,z7,z143,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z144]),(0,[z1,z7,z3,z4,z145,z5,z6])],[(0,[z0,z1,z70,z7,z3,z4,z5]),(0,[z1,z7,z146,z3,z4,z5,z6]),(0,[z1,z7,z147,z3,z4,z5,z6]),(0,[z1,z7,z148,z3,z4,z5,z6])],[(0,[z120,z1,z68,z3,z4,z5,z6]),(0,[z1,z7,z3,z149,z4,z5,z6]),(0,[z1,z7,z3,z107,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z91,z6]),(0,[z1,z7,z3,z4,z150,z5,z6]),(0,[z1,z7,z3,z151,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z85])],[(0,[z0,z1,z7,z3,z4,z5,z85]),(0,[z1,z7,z152,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z153]),(0,[z1,z7,z84,z3,z4,z5,z127])],[(1,[z97,z7,z3,z4,z30,z6])],[(0,[z1,z7,z3,z4,z5,z154,z6]),(0,[z1,z7,z3,z155,z4,z5,z6]),(0,[z1,z7,z3,z126,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z156,z6]),(0,[z1,z157,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z127,z6])],[(0,[z1,z7,z3,z158,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z159,z6]),(0,[z1,z7,z3,z4,z5,z5,z6])]],
   [[(0,[z160,z1,z7,z3,z4,z5,z6]),(0,[z161,z1,z7,z3,z4,z5,z6]),(0,[z1,z162,z7,z3,z4,z5,z103]),(0,[z1,z7,z3,z4,z5,z163,z6]),(1,[z1,z7,z3,z4,z6,z135])],[(0,[z1,z164,z7,z106,z3,z4,z5]),(0,[z1,z7,z3,z4,z165,z5,z6]),(0,[z1,z7,z3,z4,z5,z166,z6]),(0,[z1,z7,z3,z4,z5,z127,z52]),(0,[z1,z167,z7,z3,z4,z5,z6]),(0,[z168,z1,z7,z3,z4,z5,z6])],[(0,[z120,z7,z106,z3,z4,z5,z6]),(0,[z1,z162,z7,z3,z4,z5,z6]),(0,[z1,z162,z7,z3,z4,z169,z6]),(0,[z1,z7,z138,z3,z4,z5,z139]),(0,[z1,z7,z3,z4,z170,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z171]),(1,[z1,z172,z3,z4,z5,z6])],[(0,[z1,z7,z173,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z174,z6])],[(0,[z47,z25,z7,z3,z4,z5,z6]),(1,[z1,z175,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z176])],[(0,[z1,z7,z3,z4,z5,z33,z9]),(1,[z1,z7,z3,z4,z5,z72]),(0,[z1,z7,z177,z3,z4,z5,z6]),(0,[z1,z7,z3,z178,z4,z5,z6])],[(0,[z1,z7,z179,z3,z4,z5,z6]),(0,[z180,z1,z7,z3,z4,z5,z6])]],
   [[(0,[z90,z1,z106,z3,z4,z5,z6])],[(0,[z47,z1,z7,z28,z4,z5,z6]),(0,[z1,z7,z3,z4,z4,z5,z6]),(0,[z181,z1,z7,z3,z4,z182,z5]),(0,[z1,z7,z183,z3,z4,z5,z6])],[(1,[z1,z7,z3,z4,z5,z6]),(0,[z120,z1,z106,z3,z4,z5,z6]),(1,[z25,z68,z3,z4,z5,z6]),(0,[z1,z162,z68,z3,z4,z5,z6]),(0,[z1,z7,z184,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z185,z5,z6]),(0,[z90,z186,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z118,z169,z6]),(0,[z1,z7,z3,z4,z118,z5,z6])],[(0,[z1,z7,z187,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z188,z6]),(0,[z1,z7,z189,z3,z4,z5,z6])],[(0,[z1,z7,z3,z69,z190,z5,z6]),(0,[z1,z7,z191,z4,z5,z30,z6]),(0,[z1,z7,z3,z192,z4,z5,z6]),(0,[z1,z7,z3,z4,z193,z5,z6]),(0,[z1,z7,z22,z3,z4,z5,z6]),(0,[z1,z7,z194,z3,z4,z5,z6])],[(0,[z47,z1,z7,z59,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z195,z6]),(0,[z0,z1,z7,z3,z4,z5,z127]),(0,[z196,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z197,z3,z4,z141,z6]),(0,[z1,z7,z198,z3,z115,z4,z6]),(0,[z199,z1,z7,z3,z4,z5,z6])],[(0,[z27,z1,z7,z74,z4,z5,z6]),(0,[z1,z7,z3,z4,z200,z5,z6]),(0,[z1,z7,z3,z4,z201,z5,z6]),(0,[z1,z7,z202,z3,z4,z5,z203]),(0,[z1,z7,z3,z204,z4,z5,z6])],[(0,[z1,z7,z3,z4,z205,z5,z6]),(0,[z1,z206,z7,z3,z4,z5,z6]),(0,[z207,z1,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z67,z6]),(0,[z208,z1,z7,z3,z4,z5,z6]),(0,[z90,z209,z7,z3,z4,z5,z6]),(0,[z90,z1,z7,z3,z107,z5,z6]),(0,[z1,z7,z198,z3,z4,z210,z6]),(0,[z1,z7,z197,z28,z4,z5,z6])],[(0,[z1,z7,z3,z211,z4,z5,z6]),(1,[z1,z7,z3,z4,z212,z6]),(1,[z1,z70,z3,z4,z5,z52]),(0,[z1,z7,z213,z3,z4,z5,z6]),(0,[z214,z1,z7,z3,z4,z5,z6])],[(0,[z47,z1,z7,z69,z4,z5,z6]),(0,[z215,z1,z175,z3,z4,z5,z6]),(0,[z1,z216,z7,z3,z4,z210,z6]),(0,[z1,z7,z3,z4,z217,z5,z6])],[(0,[z1,z7,z3,z4,z218,z5,z6]),(0,[z181,z1,z7,z3,z4,z5,z8]),(0,[z219,z1,z23,z3,z4,z5,z6]),(0,[z220,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z221]),(0,[z1,z7,z84,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z6,z135,z85]),(0,[z1,z7,z222,z3,z4,z5,z6]),(0,[z1,z7,z3,z223,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z224,z6]),(1,[z1,z7,z3,z4,z5,z225]),(1,[z1,z7,z3,z4,z5,z174])],[(0,[z1,z7,z3,z4,z76,z141,z6]),(0,[z226,z1,z7,z3,z4,z5,z6])],[(1,[z1,z7,z227,z4,z5,z6]),(0,[z1,z7,z228,z3,z4,z5,z6]),(0,[z1,z7,z198,z3,z4,z5,z139]),(0,[z1,z7,z3,z126,z4,z5,z85])],[(1,[z1,z229,z3,z4,z5,z6]),(0,[z77,z215,z7,z3,z4,z5,z6]),(0,[z215,z1,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z230,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z231,z6]),(1,[z1,z7,z198,z3,z4,z44])],[(0,[z47,z1,z229,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z232,z6]),(0,[z90,z1,z51,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z233,z5,z6])],[(0,[z1,z7,z3,z74,z4,z5,z6]),(0,[z234,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z235,z5,z6]),(0,[z1,z7,z3,z4,z5,z236,z6]),(0,[z1,z7,z3,z4,z182,z5,z52]),(0,[z1,z7,z22,z3,z69,z5,z6]),(0,[z1,z7,z3,z4,z237,z5,z6]),(0,[z1,z7,z3,z4,z5,z238,z6])],[(0,[z181,z1,z7,z3,z4,z5,z9])],[(0,[z239,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z240,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z241,z6]),(0,[z1,z7,z3,z4,z5,z6,z242]),(1,[z1,z162,z3,z4,z210,z6]),(0,[z1,z7,z3,z4,z243,z5,z6]),(0,[z1,z7,z244,z3,z4,z5,z6])],[(0,[z47,z1,z7,z245,z4,z5,z6]),(0,[z47,z1,z7,z3,z13,z5,z6]),(0,[z47,z1,z7,z23,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z8,z139]),(0,[z219,z1,z7,z59,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z246,z6])]],
   [[(0,[z1,z7,z247,z3,z4,z5,z6]),(0,[z1,z7,z248,z3,z4,z5,z6]),(0,[z1,z7,z3,z249,z4,z5,z6])],[(0,[z47,z1,z7,z3,z4,z19,z6]),(0,[z1,z7,z3,z4,z5,z6,z250])],[(0,[z1,z7,z3,z4,z251,z5,z6]),(1,[z215,z7,z3,z190,z5,z6])],[(0,[z252,z1,z7,z3,z4,z5,z6]),(0,[z1,z253,z7,z3,z4,z5,z6]),(0,[z1,z7,z254,z3,z4,z5,z6]),(0,[z27,z1,z7,z3,z4,z5,z6]),(0,[z1,z255,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z256,z6]),(0,[z257,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z258])],[(0,[z259,z1,z7,z3,z4,z5,z6]),(1,[z186,z7,z3,z4,z5,z6]),(0,[z1,z7,z260,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z261,z5,z6]),(0,[z90,z1,z7,z3,z4,z5,z232]),(0,[z1,z7,z3,z262,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z263])],[(0,[z264,z1,z7,z3,z4,z5,z6]),(0,[z1,z265,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z266])],[(0,[z215,z7,z106,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z267,z6]),(0,[z1,z7,z3,z4,z5,z268,z6]),(0,[z269,z1,z7,z3,z4,z5,z6]),(1,[z1,z270,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z271]),(0,[z272,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z182,z5,z33])]],
   [[(0,[z1,z273,z7,z3,z4,z5,z6]),(0,[z1,z70,z3,z4,z5,z52,z6]),(0,[z1,z7,z3,z4,z5,z274,z6]),(0,[z1,z7,z3,z126,z4,z5,z127])],[(0,[z0,z1,z275,z3,z4,z5,z6]),(0,[z1,z7,z3,z276,z4,z5,z6]),(0,[z1,z7,z3,z4,z277,z5,z6]),(0,[z1,z7,z71,z198,z3,z4,z6])],[(0,[z47,z1,z7,z3,z4,z5,z66]),(0,[z1,z7,z191,z3,z4,z5,z6]),(1,[z1,z7,z202,z12,z5,z6]),(0,[z1,z7,z3,z4,z5,z278,z6])],[(0,[z1,z70,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z279,z4,z5,z6]),(0,[z1,z32,z7,z3,z4,z5,z139])],[(0,[z1,z7,z3,z280,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z281]),(0,[z1,z32,z7,z138,z4,z5,z6])],[(0,[z282,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z283,z6]),(0,[z1,z7,z3,z284,z4,z5,z6]),(0,[z1,z7,z198,z3,z4,z5,z43])],[(0,[z285,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z286,z3,z4,z5,z6]),(0,[z1,z287,z7,z3,z4,z5,z6]),(0,[z1,z62,z7,z3,z4,z5,z6]),(0,[z1,z62,z7,z59,z4,z5,z6]),(0,[z1,z7,z3,z288,z4,z5,z6]),(0,[z1,z70,z7,z3,z4,z5,z52]),(0,[z1,z7,z3,z4,z289,z5,z6]),(0,[z1,z7,z3,z290,z4,z5,z6]),(0,[z1,z7,z3,z291,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z292,z6])],[(0,[z293,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z294,z3,z4,z5,z6]),(0,[z295,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z296,z6])]],
   [[(0,[z1,z7,z3,z3,z4,z5,z6]),(0,[z1,z297,z7,z3,z4,z5,z6]),(0,[z1,z7,z298,z3,z4,z5,z6])],[(0,[z27,z1,z7,z202,z4,z5,z6]),(0,[z215,z1,z7,z3,z190,z5,z6]),(0,[z219,z1,z7,z23,z4,z5,z6]),(0,[z1,z7,z299,z3,z4,z5,z6]),(0,[z1,z117,z7,z3,z101,z5,z6]),(0,[z1,z7,z3,z300,z4,z5,z6]),(1,[z1,z51,z3,z4,z5,z53]),(0,[z1,z7,z3,z4,z301,z5,z6]),(1,[z1,z302,z3,z4,z5,z6])],[(0,[z1,z68,z7,z3,z4,z5,z6]),(0,[z303,z1,z7,z3,z4,z5,z6]),(0,[z304,z1,z7,z3,z4,z5,z6]),(0,[z1,z51,z7,z3,z4,z5,z139]),(0,[z1,z70,z7,z3,z4,z212,z6])],[(0,[z1,z70,z68,z3,z4,z5,z6]),(0,[z305,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z306,z5,z6]),(0,[z90,z1,z7,z307,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z308,z6])],[],[(0,[z27,z1,z7,z245,z4,z5,z6]),(0,[z1,z7,z202,z3,z4,z5,z309]),(1,[z1,z7,z197,z4,z301,z6]),(0,[z1,z7,z3,z4,z5,z310,z6])],[(0,[z1,z172,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z311,z5,z6]),(1,[z1,z3,z4,z5,z6,z312])]],
   [[(0,[z1,z313,z7,z3,z4,z5,z6]),(0,[z1,z7,z71,z3,z4,z118,z6]),(0,[z1,z7,z3,z4,z314,z5,z6])],[(0,[z1,z7,z315,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z316]),(0,[z1,z7,z3,z4,z5,z317,z6]),(0,[z1,z302,z3,z4,z5,z6,z85])],[(0,[z1,z7,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z318,z4,z5,z6]),(1,[z1,z62,z59,z4,z5,z6]),(0,[z90,z1,z3,z4,z210,z5,z6]),(0,[z1,z70,z7,z3,z4,z5,z33]),(0,[z1,z7,z3,z4,z319,z5,z6])],[(0,[z47,z1,z7,z74,z4,z5,z6]),(0,[z1,z7,z3,z4,z320,z5,z6])],[(0,[z25,z215,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z321,z4,z5,z6]),(0,[z1,z7,z3,z4,z322,z5,z6]),(0,[z1,z51,z3,z4,z5,z6,z53]),(0,[z323,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z324,z4,z5,z6])],[(0,[z1,z7,z3,z325,z4,z5,z6]),(0,[z1,z3,z4,z210,z5,z169,z6]),(0,[z1,z7,z3,z4,z5,z6,z326]),(1,[z1,z7,z3,z4,z182,z43])],[(0,[z1,z68,z7,z227,z4,z5,z6]),(0,[z1,z327,z7,z3,z4,z5,z6]),(0,[z1,z7,z328,z3,z4,z5,z6]),(0,[z1,z7,z3,z329,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z330]),(0,[z331,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z332,z6]),(0,[z1,z7,z3,z4,z333,z5,z6]),(1,[z1,z7,z138,z4,z5,z139]),(0,[z1,z7,z3,z115,z4,z118,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z33,z8]),(0,[z1,z62,z7,z23,z4,z5,z6]),(0,[z334,z1,z7,z3,z4,z5,z6]),(0,[z335,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z336,z6]),(0,[z1,z216,z162,z3,z4,z5,z6]),(0,[z1,z7,z28,z3,z4,z5,z6]),(0,[z1,z7,z198,z3,z4,z182,z6]),(0,[z337,z1,z7,z3,z4,z5,z6])],[(0,[z1,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z338,z3,z4,z5,z6]),(0,[z339,z1,z7,z3,z4,z5,z6]),(0,[z90,z1,z7,z340,z4,z5,z6]),(0,[z1,z7,z3,z341,z4,z5,z6])],[(0,[z1,z70,z106,z3,z4,z5,z6]),(0,[z90,z1,z117,z3,z4,z5,z6]),(0,[z1,z216,z3,z4,z5,z169,z6])],[(0,[z1,z7,z3,z4,z301,z30,z6]),(0,[z1,z7,z342,z3,z4,z5,z6]),(0,[z343,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z344]),(0,[z1,z7,z3,z4,z5,z345,z6])],[(0,[z1,z7,z3,z190,z4,z5,z346]),(0,[z1,z7,z3,z347,z4,z5,z6]),(0,[z1,z7,z3,z4,z348,z5,z6])],[(0,[z1,z7,z3,z349,z4,z5,z6]),(0,[z1,z7,z3,z4,z350,z5,z6])],[(0,[z1,z7,z229,z3,z4,z5,z6]),(0,[z1,z7,z351,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z352])]],
   [[(0,[z353,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z354,z6]),(1,[z1,z7,z3,z4,z91,z6])],[(0,[z1,z7,z3,z4,z355,z5,z6]),(0,[z1,z7,z3,z4,z101,z5,z6]),(0,[z1,z7,z84,z198,z3,z4,z5]),(0,[z1,z7,z356,z3,z4,z5,z6])],[(0,[z1,z7,z3,z26,z12,z5,z6]),(0,[z1,z357,z7,z3,z4,z5,z6]),(0,[z1,z7,z358,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z359,z5,z6]),(0,[z1,z7,z3,z4,z169,z43,z6]),(0,[z1,z7,z360,z3,z4,z5,z6]),(0,[z1,z7,z3,z361,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z362,z6]),(0,[z1,z7,z3,z4,z363,z5,z6]),(0,[z1,z7,z198,z3,z4,z5,z44])],[(0,[z364,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z365,z6]),(0,[z1,z7,z3,z4,z30,z141,z6]),(0,[z1,z7,z366,z3,z4,z5,z6]),(0,[z367,z1,z7,z3,z4,z5,z6])],[(0,[z368,z1,z7,z3,z4,z5,z6]),(0,[z369,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z370,z3,z4,z5,z6]),(1,[z1,z7,z371,z3,z4,z6])],[(0,[z181,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z372,z6]),(0,[z1,z7,z3,z4,z5,z373,z6]),(0,[z1,z3,z4,z5,z308,z41,z6])],[(0,[z1,z7,z3,z374,z4,z5,z6]),(0,[z0,z7,z3,z4,z5,z6,z9]),(0,[z1,z7,z3,z375,z4,z5,z6])]],
   [[(0,[z47,z1,z7,z3,z4,z5,z6]),(0,[z29,z1,z7,z3,z4,z76,z6]),(0,[z1,z7,z3,z4,z376,z5,z6]),(0,[z1,z7,z3,z4,z5,z52,z85])],[(0,[z1,z377,z7,z3,z4,z5,z6]),(0,[z1,z63,z7,z106,z3,z4,z5]),(0,[z47,z1,z7,z4,z301,z5,z6]),(0,[z181,z0,z7,z3,z4,z5,z6]),(1,[z1,z275,z3,z4,z5,z6]),(0,[z1,z378,z7,z3,z4,z5,z6]),(0,[z1,z379,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z380]),(0,[z1,z7,z3,z4,z5,z33,z85]),(0,[z1,z7,z3,z4,z5,z381,z6])],[(0,[z1,z7,z106,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z382]),(0,[z1,z7,z383,z3,z4,z5,z6]),(0,[z384,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z385]),(0,[z386,z1,z7,z3,z4,z5,z6]),(0,[z387,z1,z7,z3,z4,z5,z6])],[(0,[z7,z245,z3,z74,z4,z5,z6]),(0,[z1,z7,z4,z301,z5,z141,z6])],[(0,[z1,z388,z7,z3,z4,z5,z6]),(0,[z1,z117,z7,z3,z107,z5,z6]),(0,[z1,z7,z3,z389,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z390])],[(0,[z1,z7,z3,z391,z4,z5,z6]),(0,[z1,z7,z3,z4,z392,z5,z6]),(1,[z1,z7,z3,z4,z5,z283])],[(0,[z393,z1,z7,z3,z4,z5,z6])],[(1,[z47,z7,z74,z4,z5,z6]),(0,[z1,z7,z394,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z395]),(0,[z1,z7,z3,z4,z116,z5,z6]),(0,[z1,z7,z197,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z396,z4,z5,z6]),(0,[z1,z51,z3,z107,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z330]),(0,[z1,z7,z3,z4,z5,z397,z6]),(0,[z398,z1,z7,z3,z4,z5,z6]),(0,[z1,z399,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z72,z6]),(0,[z1,z400,z7,z3,z4,z5,z6])],[(0,[z1,z7,z84,z3,z126,z5,z6]),(0,[z1,z7,z3,z4,z5,z401,z6])],[(1,[z1,z7,z402,z3,z4,z5]),(0,[z0,z1,z7,z198,z3,z4,z5]),(0,[z403,z1,z7,z3,z4,z5,z6]),(0,[z90,z1,z216,z3,z4,z5,z6]),(0,[z1,z7,z202,z3,z12,z5,z6])],[(0,[z77,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z404,z5,z6]),(0,[z1,z7,z3,z4,z5,z203,z6]),(0,[z1,z7,z3,z405,z4,z5,z6]),(0,[z1,z7,z71,z3,z4,z5,z406]),(0,[z1,z7,z3,z4,z5,z85,z44])],[(0,[z1,z162,z106,z3,z4,z5,z6]),(0,[z1,z7,z3,z407,z4,z5,z6]),(0,[z1,z7,z3,z408,z4,z5,z6]),(0,[z1,z409,z7,z3,z4,z5,z6]),(0,[z1,z410,z7,z3,z4,z5,z6]),(0,[z1,z7,z411,z3,z4,z5,z6])],[(0,[z47,z1,z7,z202,z4,z5,z6]),(0,[z412,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z76,z5,z6]),(0,[z1,z7,z413,z3,z4,z5,z6]),(0,[z1,z7,z414,z3,z4,z5,z6])]],
   [[(0,[z47,z7,z106,z3,z4,z5,z6]),(0,[z415,z1,z7,z3,z4,z5,z6]),(0,[z196,z219,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z416]),(0,[z1,z7,z3,z4,z5,z417,z6]),(0,[z1,z418,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z419,z6]),(0,[z420,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z421,z5,z6]),(0,[z1,z422,z7,z3,z4,z5,z6])],[(0,[z0,z1,z51,z7,z3,z4,z5]),(0,[z219,z1,z7,z3,z4,z5,z6]),(0,[z1,z3,z107,z4,z210,z5,z6])],[(0,[z1,z7,z423,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z33,z127])],[(0,[z424,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z290,z4,z5]),(1,[z1,z7,z3,z115,z118,z6])],[(0,[z1,z7,z3,z4,z5,z425,z6]),(0,[z1,z7,z3,z4,z5,z426,z6]),(0,[z181,z1,z70,z7,z3,z4,z5]),(0,[z1,z7,z3,z4,z5,z427,z6])],[(0,[z1,z7,z3,z4,z428,z5,z6]),(0,[z429,z1,z7,z3,z4,z5,z6]),(0,[z1,z430,z7,z3,z4,z5,z6]),(0,[z431,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z432])],[(0,[z27,z1,z7,z4,z301,z5,z6]),(0,[z97,z1,z7,z3,z4,z5,z6]),(0,[z181,z1,z7,z3,z4,z5,z85]),(0,[z1,z7,z3,z433,z4,z5,z6]),(0,[z1,z434,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z312])]],
   [[(0,[z1,z7,z138,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z435,z5,z6])],[(0,[z436,z1,z7,z3,z4,z5,z6])],[(0,[z219,z1,z68,z3,z4,z5,z6]),(0,[z1,z7,z95,z3,z4,z5,z6]),(1,[z219,z1,z23,z4,z5,z6]),(0,[z1,z7,z307,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z437,z6]),(0,[z1,z7,z438,z3,z4,z5,z6]),(1,[z196,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z439]),(0,[z1,z7,z440,z3,z4,z5,z6])],[(0,[z441,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z442,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z443,z6]),(0,[z444,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z445,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z446])],[(0,[z447,z1,z7,z3,z4,z5,z6]),(1,[z209,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z448,z4,z5,z6]),(0,[z1,z7,z3,z449,z4,z5,z6])],[(0,[z1,z7,z450,z3,z4,z5,z6]),(0,[z1,z7,z3,z451,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z452,z6]),(0,[z1,z7,z3,z4,z210,z43,z6]),(0,[z1,z7,z69,z4,z12,z5,z6])],[(0,[z1,z7,z3,z4,z453,z5,z6]),(0,[z1,z7,z454,z3,z4,z5,z6]),(0,[z455,z1,z7,z3,z4,z5,z6]),(0,[z90,z1,z7,z3,z4,z350,z6]),(0,[z1,z7,z3,z4,z5,z456,z6]),(0,[z1,z7,z3,z4,z5,z457,z6]),(0,[z1,z7,z3,z4,z182,z5,z139])]],
   [[(0,[z1,z7,z3,z458,z4,z5,z6]),(0,[z1,z7,z3,z459,z4,z5,z6]),(1,[z1,z7,z3,z453,z5,z6]),(0,[z1,z7,z3,z4,z460,z5,z6]),(0,[z1,z7,z461,z3,z4,z5,z6]),(0,[z1,z7,z198,z3,z4,z6,z44])],[(1,[z120,z106,z3,z4,z5,z6]),(0,[z25,z68,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z462,z5,z6]),(0,[z1,z7,z3,z190,z12,z5,z6]),(0,[z1,z7,z28,z3,z4,z301,z6]),(0,[z1,z7,z3,z4,z5,z174,z41])],[(0,[z1,z7,z3,z4,z463,z5,z6]),(0,[z1,z7,z3,z4,z5,z141,z6]),(0,[z1,z464,z7,z3,z4,z5,z6]),(0,[z1,z465,z7,z3,z4,z5,z6])],[(0,[z466,z1,z7,z3,z4,z5,z6]),(0,[z47,z1,z7,z3,z453,z5,z6]),(0,[z1,z7,z467,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z468,z6]),(1,[z1,z7,z191,z4,z5,z6]),(1,[z29,z7,z3,z4,z76,z6]),(0,[z469,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z470,z3,z4,z5,z6])],[(0,[z7,z3,z190,z4,z26,z5,z6]),(0,[z1,z7,z3,z471,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z472,z6]),(0,[z1,z7,z3,z4,z5,z6,z473]),(0,[z474,z1,z7,z3,z4,z5,z6]),(1,[z1,z216,z3,z4,z169,z6]),(0,[z1,z7,z3,z4,z475,z5,z6]),(0,[z1,z162,z7,z3,z4,z5,z390]),(0,[z1,z7,z202,z22,z4,z5,z6])],[(0,[z27,z7,z245,z3,z4,z5,z6]),(0,[z77,z1,z7,z3,z190,z5,z6]),(0,[z476,z1,z7,z3,z4,z5,z6])],[(0,[z215,z7,z3,z190,z4,z5,z6]),(1,[z477,z7,z3,z4,z5,z6]),(0,[z1,z7,z478,z3,z4,z5,z6]),(0,[z1,z7,z202,z4,z12,z5,z6]),(0,[z1,z7,z138,z3,z4,z5,z33])]],
   [[(0,[z1,z7,z175,z3,z4,z5,z6]),(0,[z1,z7,z479,z3,z4,z5,z6]),(0,[z1,z7,z480,z3,z4,z5,z6]),(0,[z1,z7,z3,z481,z4,z5,z6])],[(0,[z1,z7,z227,z3,z4,z5,z6]),(0,[z1,z7,z3,z482,z4,z5,z6]),(0,[z181,z1,z7,z3,z4,z5,z127]),(0,[z1,z7,z198,z3,z4,z5,z53]),(1,[z1,z7,z28,z4,z141,z6]),(0,[z1,z7,z3,z4,z5,z483,z6]),(0,[z1,z302,z7,z3,z4,z5,z6])],[(0,[z219,z1,z106,z3,z4,z5,z6]),(0,[z97,z1,z7,z3,z4,z30,z6]),(0,[z1,z7,z484,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z52,z6]),(0,[z1,z7,z71,z3,z5,z41,z6])],[(0,[z1,z7,z3,z4,z485,z5,z6]),(0,[z1,z7,z3,z4,z486,z5,z6]),(0,[z215,z1,z230,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z33,z6]),(0,[z1,z7,z3,z4,z5,z6,z139]),(0,[z1,z7,z3,z4,z487,z5,z6]),(0,[z1,z7,z488,z3,z4,z5,z6])],[(1,[z1,z489,z3,z4,z5,z6]),(0,[z1,z7,z3,z490,z4,z5,z6]),(0,[z1,z7,z198,z3,z4,z169,z6]),(0,[z1,z7,z3,z4,z5,z491,z6]),(0,[z1,z7,z3,z4,z5,z43,z85]),(1,[z1,z7,z3,z126,z5,z127]),(0,[z1,z7,z198,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z182,z43,z6])],[(1,[z1,z7,z3,z4,z5,z390])],[(0,[z1,z7,z492,z3,z4,z5,z6]),(1,[z1,z7,z4,z493,z5,z6]),(0,[z1,z216,z7,z3,z4,z5,z6]),(0,[z1,z216,z7,z3,z4,z169,z6]),(0,[z1,z7,z494,z3,z4,z5,z6])],[(0,[z1,z7,z3,z495,z4,z5,z6]),(0,[z1,z7,z3,z4,z496,z5,z6]),(0,[z1,z7,z3,z4,z497,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z498,z5,z6])],[(0,[z25,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z499,z5,z6]),(0,[z500,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z275,z3,z4,z5,z6]),(0,[z1,z216,z3,z107,z4,z5,z6]),(0,[z1,z7,z3,z5,z127,z6,z85])],[(0,[z1,z7,z3,z340,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z232]),(0,[z1,z7,z3,z4,z169,z41,z6]),(0,[z1,z7,z3,z4,z5,z501,z6]),(0,[z1,z7,z3,z4,z5,z502,z6]),(0,[z1,z7,z198,z3,z126,z4,z5])],[(0,[z1,z7,z3,z4,z5,z503,z6])],[(0,[z97,z1,z270,z3,z4,z5,z6])],[(0,[z1,z7,z4,z493,z5,z30,z6]),(0,[z1,z7,z3,z4,z5,z8,z6]),(0,[z1,z7,z3,z4,z504,z5,z6]),(0,[z1,z7,z505,z3,z4,z5,z6]),(0,[z1,z7,z371,z3,z4,z6,z85])],[(0,[z1,z7,z3,z69,z26,z5,z6]),(0,[z1,z7,z506,z3,z4,z5,z6]),(0,[z1,z270,z7,z3,z4,z5,z6]),(0,[z90,z1,z7,z3,z4,z5,z64]),(0,[z1,z7,z3,z4,z5,z507,z6]),(0,[z1,z7,z3,z4,z182,z5,z43])],[(1,[z1,z7,z508,z4,z5,z6]),(0,[z509,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z197,z3,z4,z301,z6]),(0,[z1,z7,z3,z4,z5,z6,z510]),(0,[z1,z7,z3,z4,z5,z511,z6])]],
   [[(0,[z1,z7,z512,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z513,z5,z6]),(0,[z1,z7,z3,z4,z5,z514,z6]),(0,[z1,z7,z3,z4,z515,z5,z6])],[(0,[z25,z1,z68,z3,z4,z5,z6]),(0,[z1,z516,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z517,z5,z6])],[(0,[z1,z7,z518,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z519,z5,z6]),(0,[z1,z7,z371,z3,z4,z5,z6])],[(0,[z1,z7,z520,z3,z4,z5,z6]),(0,[z1,z7,z23,z3,z4,z5,z521]),(0,[z1,z7,z3,z4,z522,z5,z6]),(0,[z523,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z197,z3,z4,z5,z330])],[(0,[z1,z7,z3,z4,z5,z524,z6]),(0,[z97,z29,z7,z3,z4,z5,z6]),(0,[z525,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z202,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z203]),(0,[z1,z7,z3,z4,z5,z6,z526]),(0,[z1,z3,z4,z5,z6,z312,z85])],[(0,[z25,z120,z7,z3,z4,z5,z6]),(0,[z1,z7,z527,z3,z4,z5,z6]),(0,[z1,z528,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z529]),(0,[z1,z7,z530,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z531,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z532]),(0,[z1,z7,z533,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z43,z127]),(0,[z1,z7,z534,z3,z4,z5,z6])],[(0,[z1,z106,z3,z4,z5,z6,z53]),(0,[z1,z7,z3,z4,z535,z5,z6]),(0,[z1,z7,z536,z3,z4,z5,z6]),(1,[z1,z98,z3,z4,z5,z6]),(0,[z1,z7,z3,z537,z4,z5,z6]),(0,[z1,z7,z3,z538,z4,z5,z6]),(0,[z1,z7,z539,z3,z4,z5,z6]),(0,[z1,z162,z3,z4,z210,z5,z6]),(0,[z540,z1,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z541,z3,z4,z5,z6]),(1,[z1,z7,z307,z4,z5,z6]),(0,[z1,z7,z71,z3,z4,z43,z6]),(0,[z1,z7,z3,z542,z4,z5,z6])],[(0,[z7,z106,z245,z3,z4,z5,z6]),(0,[z25,z7,z245,z3,z4,z5,z6]),(0,[z181,z7,z3,z4,z5,z8,z6]),(0,[z1,z543,z7,z3,z4,z5,z6]),(0,[z1,z32,z7,z3,z4,z5,z6])],[(0,[z1,z164,z7,z3,z4,z5,z6]),(0,[z544,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z545]),(0,[z219,z1,z62,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z546])],[(0,[z1,z7,z3,z547,z4,z5,z6]),(0,[z1,z23,z3,z59,z4,z5,z6]),(0,[z1,z548,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z549,z5,z6])],[(0,[z1,z550,z7,z3,z4,z5,z6]),(0,[z1,z7,z245,z3,z4,z5,z6]),(0,[z551,z1,z7,z3,z4,z5,z6]),(0,[z1,z51,z7,z3,z4,z5,z53]),(0,[z1,z7,z552,z3,z4,z5,z6]),(1,[z1,z7,z84,z3,z5,z85])],[(0,[z1,z7,z3,z553,z4,z5,z6]),(0,[z554,z1,z7,z3,z4,z5,z6]),(0,[z1,z162,z7,z3,z4,z210,z6]),(0,[z555,z1,z7,z3,z4,z5,z6]),(0,[z1,z172,z3,z4,z5,z41,z6])],[(0,[z1,z7,z3,z556,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z406]),(0,[z1,z7,z3,z115,z4,z43,z6])]],
   [[(0,[z1,z7,z3,z557,z4,z5,z6]),(0,[z1,z7,z3,z558,z4,z5,z6]),(1,[z1,z7,z3,z4,z48,z6]),(0,[z1,z7,z3,z4,z559,z5,z6]),(1,[z0,z7,z3,z4,z5,z9]),(0,[z1,z7,z3,z4,z5,z560,z6]),(0,[z1,z7,z561,z3,z4,z5,z6]),(0,[z1,z51,z7,z3,z4,z5,z6]),(0,[z1,z70,z51,z3,z4,z5,z6]),(0,[z1,z7,z562,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z127,z139])],[(0,[z25,z1,z106,z3,z4,z5,z6]),(0,[z68,z7,z106,z3,z4,z5,z6]),(0,[z7,z106,z3,z4,z26,z5,z6]),(0,[z1,z7,z3,z4,z5,z563,z6]),(0,[z1,z7,z402,z3,z4,z5,z30]),(0,[z1,z7,z3,z4,z564,z5,z6])],[(0,[z1,z7,z565,z3,z4,z5,z6])],[(0,[z566,z1,z7,z3,z4,z5,z6]),(0,[z1,z567,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z568,z6]),(0,[z1,z7,z3,z4,z5,z569,z6]),(0,[z1,z7,z3,z4,z5,z570,z6]),(0,[z1,z7,z202,z3,z69,z5,z6]),(0,[z1,z7,z197,z4,z301,z5,z6]),(0,[z1,z7,z3,z290,z4,z5,z41])],[(0,[z571,z1,z7,z3,z4,z5,z6]),(0,[z572,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z573,z5,z6]),(0,[z1,z7,z3,z4,z5,z521,z6]),(0,[z1,z574,z7,z3,z4,z5,z6]),(0,[z1,z7,z4,z5,z33,z6,z139]),(0,[z1,z7,z575,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z576])],[(0,[z1,z7,z3,z4,z26,z5,z6]),(0,[z0,z1,z7,z3,z4,z182,z5]),(0,[z1,z577,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z578,z6]),(0,[z1,z106,z3,z59,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z67]),(0,[z579,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z118,z210,z6])],[(0,[z1,z7,z3,z580,z4,z5,z6]),(0,[z1,z7,z23,z3,z4,z5,z10]),(1,[z1,z7,z340,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z581,z6]),(0,[z1,z7,z3,z4,z5,z582,z6]),(0,[z583,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z584,z3,z4,z5,z6]),(0,[z1,z7,z585,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z586,z6])]],
   [[(0,[z1,z32,z7,z3,z4,z5,z33]),(0,[z1,z7,z587,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z588,z6]),(0,[z1,z7,z3,z4,z5,z6,z589]),(0,[z590,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z591,z5,z6]),(0,[z1,z3,z107,z4,z101,z5,z6]),(0,[z592,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z593,z6])],[(0,[z1,z7,z594,z3,z4,z5,z6]),(0,[z1,z7,z3,z190,z4,z5,z6]),(0,[z1,z7,z3,z4,z595,z5,z6]),(0,[z1,z7,z197,z3,z4,z5,z283])],[],[(0,[z1,z7,z3,z4,z493,z5,z6]),(0,[z1,z7,z3,z4,z182,z5,z44])],[(0,[z1,z596,z7,z3,z4,z5,z6]),(0,[z1,z209,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z210,z41,z6]),(0,[z1,z7,z3,z4,z5,z597,z6])],[(0,[z1,z7,z3,z4,z598,z5,z6]),(0,[z1,z7,z3,z4,z5,z43,z6])],[(0,[z1,z7,z3,z4,z5,z599,z6]),(1,[z1,z7,z3,z4,z116,z5]),(0,[z0,z1,z7,z3,z4,z5,z8]),(0,[z1,z51,z7,z3,z4,z5,z33])]],
   [[(0,[z1,z7,z59,z4,z12,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z600])],[(0,[z1,z601,z7,z3,z4,z5,z6]),(0,[z1,z7,z602,z3,z4,z5,z6])],[(1,[z1,z7,z3,z4,z5,z521]),(0,[z1,z603,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z604,z6]),(0,[z1,z7,z3,z605,z4,z5,z6]),(1,[z1,z7,z71,z3,z41,z6])],[(0,[z215,z1,z7,z3,z26,z5,z6]),(0,[z1,z7,z3,z4,z5,z9,z139])],[(0,[z1,z7,z3,z13,z4,z5,z6]),(0,[z1,z7,z3,z190,z4,z5,z225]),(0,[z1,z7,z3,z4,z5,z6,z606])],[(0,[z1,z7,z3,z508,z4,z5,z6]),(1,[z1,z7,z96,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z346]),(0,[z607,z1,z7,z3,z4,z5,z6]),(0,[z90,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z118,z5,z41,z6])],[(0,[z1,z608,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z609]),(0,[z1,z7,z610,z3,z4,z5,z6])],[(1,[z1,z164,z7,z3,z4,z5]),(0,[z1,z68,z7,z508,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z9]),(0,[z1,z477,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z611,z6]),(0,[z1,z7,z3,z4,z5,z6,z612])]],
   [[(0,[z1,z106,z3,z4,z5,z169,z6]),(0,[z0,z1,z7,z3,z4,z5,z9]),(0,[z1,z7,z3,z613,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z44])],[(1,[z1,z230,z3,z4,z5,z6]),(0,[z1,z7,z614,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z615,z5,z6])],[(0,[z1,z7,z3,z4,z616,z5,z6]),(1,[z1,z7,z3,z4,z5,z309]),(0,[z1,z7,z3,z4,z5,z617,z6]),(0,[z1,z7,z618,z3,z4,z5,z6])],[(0,[z1,z68,z3,z4,z5,z169,z6]),(0,[z1,z7,z3,z4,z5,z619,z6]),(0,[z7,z3,z4,z76,z5,z30,z6]),(0,[z1,z7,z620,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z621,z5,z6])],[(0,[z90,z1,z68,z3,z4,z5,z6]),(0,[z1,z7,z622,z3,z4,z5,z6])],[(0,[z1,z623,z7,z3,z4,z5,z6])],[(0,[z77,z7,z3,z4,z26,z5,z6]),(0,[z1,z7,z3,z624,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z301,z76,z6]),(0,[z1,z7,z3,z4,z5,z127,z53]),(0,[z625,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z126,z4,z182,z5])],[],[(0,[z626,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z64])],[(0,[z1,z7,z3,z4,z5,z6,z66]),(0,[z627,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z628]),(0,[z1,z7,z629,z3,z4,z5,z6])],[(0,[z1,z7,z402,z3,z4,z5,z6]),(0,[z1,z7,z3,z630,z4,z5,z6]),(0,[z1,z7,z3,z4,z631,z5,z6]),(0,[z90,z1,z3,z4,z101,z5,z6]),(0,[z1,z7,z3,z4,z5,z169,z6]),(0,[z1,z7,z632,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z53,z85])],[(0,[z633,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z634,z6]),(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z3,z635,z4,z5,z6])],[(1,[z27,z7,z245,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z10]),(0,[z1,z7,z3,z4,z5,z636,z6])],[(0,[z1,z7,z98,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z637])]],
   [[(0,[z1,z7,z3,z4,z5,z638,z6]),(1,[z1,z117,z3,z107,z5,z6]),(1,[z1,z7,z3,z4,z5,z406]),(1,[z1,z3,z4,z5,z308,z6])],[(0,[z1,z7,z3,z4,z639,z5,z6]),(0,[z1,z7,z3,z4,z5,z225,z6]),(0,[z1,z7,z3,z4,z5,z640,z6]),(0,[z1,z7,z3,z641,z4,z5,z6]),(0,[z1,z7,z84,z3,z5,z6,z85])],[(0,[z47,z1,z489,z3,z4,z5,z6]),(0,[z1,z7,z3,z642,z4,z5,z6]),(0,[z1,z7,z198,z3,z4,z5,z52])],[(0,[z186,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z643,z5,z6]),(0,[z1,z7,z644,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z645]),(0,[z1,z7,z646,z3,z4,z5,z6])],[(0,[z1,z647,z7,z3,z4,z5,z6]),(0,[z1,z7,z648,z3,z4,z5,z6]),(0,[z1,z649,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z650,z5,z6]),(0,[z1,z7,z3,z4,z5,z651,z6]),(1,[z1,z7,z3,z4,z5,z103]),(0,[z1,z70,z7,z3,z4,z5,z139]),(0,[z1,z652,z7,z3,z4,z5,z6])],[(0,[z1,z7,z653,z3,z4,z5,z6]),(0,[z1,z654,z7,z3,z4,z5,z6]),(0,[z1,z7,z655,z3,z4,z5,z6]),(0,[z1,z656,z7,z3,z4,z5,z6]),(0,[z1,z7,z28,z4,z5,z141,z6]),(0,[z657,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z658]),(0,[z1,z7,z3,z4,z5,z6,z346]),(0,[z181,z1,z7,z198,z3,z4,z5]),(0,[z1,z7,z3,z4,z5,z6,z659]),(0,[z1,z7,z3,z4,z210,z5,z6]),(0,[z1,z7,z3,z4,z5,z660,z6]),(0,[z1,z7,z3,z4,z661,z5,z6]),(0,[z1,z7,z71,z3,z4,z41,z6]),(0,[z662,z1,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z663,z6]),(0,[z1,z2,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z133,z6]),(0,[z1,z7,z3,z4,z5,z6,z664]),(0,[z1,z7,z3,z4,z5,z6,z665])],[(0,[z1,z7,z3,z4,z5,z6,z666]),(0,[z29,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z22,z59,z4,z5,z6]),(0,[z1,z7,z3,z667,z4,z5,z6]),(0,[z1,z7,z3,z668,z4,z5,z6])],[(0,[z1,z669,z7,z3,z4,z5,z6]),(0,[z1,z670,z7,z3,z4,z5,z6]),(0,[z1,z7,z671,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z672,z5,z6]),(0,[z1,z673,z7,z3,z4,z5,z6])],[(0,[z1,z7,z674,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z675,z5,z6])],[(1,[z1,z7,z3,z4,z350,z6]),(0,[z1,z7,z3,z4,z212,z5,z6])],[(0,[z1,z676,z7,z3,z4,z5,z6]),(0,[z1,z7,z677,z3,z4,z5,z6]),(0,[z1,z7,z678,z3,z4,z5,z6]),(0,[z1,z679,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z309]),(0,[z1,z7,z3,z4,z5,z127,z44])],[(0,[z1,z7,z3,z680,z4,z5,z6]),(0,[z181,z1,z51,z7,z3,z4,z5]),(0,[z1,z7,z22,z69,z4,z5,z6]),(0,[z1,z7,z198,z3,z4,z5,z33]),(0,[z1,z7,z3,z115,z4,z41,z6]),(0,[z1,z7,z84,z3,z4,z182,z5])],[(0,[z1,z681,z7,z3,z4,z5,z6]),(0,[z1,z682,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z48,z5,z6]),(0,[z1,z7,z683,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z30,z6]),(0,[z1,z7,z3,z4,z684,z5,z6]),(0,[z219,z477,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z685,z5,z6]),(0,[z686,z1,z7,z3,z4,z5,z6]),(0,[z687,z1,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z19,z6]),(1,[z181,z7,z3,z4,z5,z8]),(0,[z1,z7,z3,z4,z688,z5,z6]),(0,[z1,z7,z3,z4,z689,z5,z6])],[(1,[z1,z63,z7,z3,z4,z5]),(0,[z1,z489,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z690]),(0,[z1,z7,z3,z4,z5,z691,z6]),(0,[z1,z692,z7,z3,z4,z5,z6])],[(0,[z1,z693,z7,z3,z4,z5,z6]),(0,[z1,z3,z107,z4,z5,z52,z6]),(0,[z1,z7,z3,z4,z182,z5,z53]),(0,[z1,z694,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z695]),(0,[z1,z696,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z96,z4,z5,z6]),(0,[z1,z7,z697,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z133,z6])],[(0,[z698,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z699,z3,z4,z5,z6])],[(1,[z90,z1,z3,z101,z5,z6]),(0,[z1,z7,z3,z700,z4,z5,z6]),(0,[z1,z7,z3,z4,z182,z5,z6])],[(0,[z1,z68,z3,z4,z5,z6,z53]),(0,[z1,z7,z701,z3,z4,z5,z6]),(0,[z1,z7,z23,z4,z12,z5,z6]),(0,[z1,z702,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z703,z4,z5,z6]),(0,[z1,z7,z95,z4,z26,z5,z6]),(0,[z1,z704,z7,z3,z4,z5,z6]),(0,[z1,z7,z705,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z139,z85]),(0,[z706,z1,z7,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z7,z3,z4,z5,z707]),(0,[z708,z7,z3,z4,z5,z6]),(0,[z1,z32,z7,z4,z5,z33])],[(0,[z1,z7,z709,z4,z5,z6]),(0,[z7,z3,z710,z4,z5,z6])],[(0,[z1,z7,z3,z13,z5,z66]),(0,[z1,z7,z3,z4,z711,z6]),(0,[z1,z7,z3,z4,z5,z309]),(0,[z1,z7,z4,z712,z141,z6])],[(0,[z1,z7,z3,z4,z5,z713]),(0,[z1,z7,z714,z4,z5,z6])],[(0,[z230,z106,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z19,z66]),(0,[z1,z7,z3,z4,z5,z715]),(0,[z1,z7,z3,z4,z5,z716])],[(0,[z215,z7,z3,z717,z5,z6]),(0,[z1,z7,z38,z4,z5,z139]),(0,[z1,z7,z3,z4,z5,z718]),(0,[z1,z7,z71,z3,z719,z6]),(0,[z1,z7,z3,z4,z720,z6])],[(0,[z1,z596,z3,z4,z169,z6]),(0,[z27,z7,z4,z320,z5,z6]),(0,[z1,z7,z3,z4,z6,z721])],[(0,[z1,z106,z3,z4,z5,z64]),(0,[z1,z7,z3,z717,z5,z6]),(0,[z1,z7,z95,z69,z5,z6]),(0,[z1,z7,z3,z4,z722,z6]),(0,[z1,z723,z3,z4,z5,z6])]],
   [[(0,[z7,z106,z95,z4,z5,z6]),(0,[z1,z7,z3,z4,z724,z6]),(0,[z97,z7,z3,z4,z30,z6]),(0,[z1,z7,z3,z4,z5,z725])],[(0,[z1,z7,z3,z4,z726,z6]),(0,[z1,z7,z3,z4,z727,z6]),(0,[z186,z7,z3,z4,z5,z64]),(0,[z1,z7,z3,z4,z5,z728]),(0,[z1,z7,z3,z4,z5,z729]),(0,[z1,z7,z3,z4,z5,z730])],[(0,[z1,z674,z3,z107,z5,z6]),(0,[z1,z7,z3,z4,z731,z6]),(0,[z1,z7,z3,z732,z5,z6]),(0,[z1,z7,z371,z3,z4,z43]),(0,[z1,z733,z3,z4,z5,z6])],[(0,[z1,z7,z629,z4,z5,z139]),(0,[z1,z302,z84,z3,z5,z85])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z734]),(0,[z47,z7,z74,z453,z5,z6]),(0,[z7,z710,z74,z4,z5,z6]),(0,[z1,z117,z3,z735,z5,z6]),(0,[z1,z7,z3,z4,z736,z6]),(0,[z1,z7,z198,z3,z4,z406]),(0,[z1,z7,z3,z5,z127,z737])],[(0,[z1,z7,z3,z4,z5,z10]),(0,[z1,z7,z3,z4,z738,z6])],[(0,[z209,z7,z340,z4,z5,z6]),(0,[z1,z739,z3,z4,z5,z6]),(0,[z1,z7,z84,z3,z135,z85])],[(0,[z1,z7,z3,z740,z5,z6]),(0,[z47,z7,z585,z4,z5,z6]),(0,[z387,z7,z3,z4,z5,z8]),(0,[z1,z117,z3,z107,z5,z6]),(0,[z1,z3,z4,z5,z308,z6]),(0,[z1,z172,z3,z4,z169,z6]),(0,[z1,z7,z371,z3,z4,z406])]],
   [[(0,[z1,z7,z3,z453,z5,z67]),(0,[z1,z7,z3,z4,z5,z741])],[(0,[z1,z7,z742,z4,z5,z6]),(0,[z1,z743,z3,z4,z5,z6]),(0,[z1,z744,z3,z4,z5,z6]),(0,[z1,z7,z71,z3,z496,z6])],[(0,[z745,z106,z3,z4,z5,z6]),(0,[z554,z106,z3,z4,z5,z6]),(0,[z1,z70,z63,z3,z4,z5]),(0,[z1,z746,z3,z4,z5,z6]),(0,[z1,z747,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z72])],[(0,[z1,z7,z710,z4,z5,z6])],[(0,[z1,z7,z748,z4,z5,z6]),(0,[z1,z7,z3,z4,z749,z6]),(0,[z215,z7,z3,z190,z5,z346]),(0,[z1,z7,z307,z4,z5,z232]),(0,[z750,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z103]),(0,[z1,z7,z3,z4,z169,z103]),(0,[z1,z7,z3,z115,z6,z612]),(0,[z1,z7,z3,z4,z517,z43])],[(0,[z1,z7,z751,z4,z5,z6]),(0,[z1,z216,z3,z4,z752,z6]),(0,[z1,z3,z4,z5,z753,z53])],[(0,[z1,z7,z3,z4,z5,z6]),(0,[z25,z68,z3,z4,z5,z6]),(0,[z1,z302,z3,z4,z5,z64]),(0,[z1,z754,z3,z4,z5,z6])],[(0,[z1,z7,z3,z755,z5,z6])]],
   [[(0,[z47,z489,z74,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z756]),(0,[z1,z275,z3,z4,z182,z5]),(0,[z1,z3,z4,z5,z753,z6]),(0,[z1,z7,z678,z3,z5,z85]),(0,[z1,z3,z4,z757,z5,z6]),(0,[z1,z7,z3,z4,z182,z758])],[],[(0,[z1,z7,z3,z4,z5,z759]),(0,[z1,z7,z3,z4,z212,z53]),(0,[z1,z70,z3,z4,z5,z753]),(0,[z760,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z761]),(0,[z7,z3,z4,z5,z762,z6])],[(0,[z1,z763,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z350,z6]),(0,[z1,z7,z4,z5,z764,z139])],[],[(0,[z1,z7,z3,z4,z212,z6]),(0,[z1,z70,z3,z4,z5,z52])],[],[(0,[z1,z7,z4,z5,z765,z6]),(0,[z181,z7,z3,z4,z5,z8]),(0,[z90,z1,z3,z101,z91,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z766]),(0,[z90,z1,z3,z515,z5,z6]),(0,[z1,z51,z3,z4,z5,z593]),(0,[z1,z7,z3,z4,z43,z344])],[(0,[z181,z1,z7,z3,z4,z212]),(0,[z686,z1,z23,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z767]),(0,[z1,z7,z3,z4,z133,z6]),(0,[z1,z7,z202,z12,z5,z309]),(0,[z1,z768,z3,z4,z5,z6])],[(0,[z47,z7,z557,z4,z5,z6]),(0,[z1,z229,z3,z4,z5,z6]),(0,[z47,z7,z558,z4,z5,z6]),(0,[z0,z1,z7,z3,z4,z212]),(0,[z1,z7,z340,z4,z5,z232]),(0,[z1,z7,z769,z4,z5,z6]),(0,[z1,z7,z198,z3,z4,z609])],[(0,[z1,z770,z3,z4,z5,z6]),(0,[z1,z70,z3,z4,z212,z52])],[(0,[z1,z7,z771,z4,z5,z6]),(0,[z97,z270,z3,z4,z30,z6]),(0,[z1,z7,z3,z4,z5,z772]),(0,[z1,z7,z773,z4,z5,z6]),(0,[z1,z7,z198,z3,z4,z44])],[(0,[z68,z745,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z774]),(0,[z1,z327,z7,z4,z5,z33])],[(0,[z1,z7,z3,z775,z5,z6]),(0,[z1,z776,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z13,z5,z6]),(0,[z1,z777,z3,z4,z5,z6]),(0,[z1,z778,z3,z4,z5,z6]),(0,[z1,z7,z3,z290,z4,z169]),(0,[z1,z162,z3,z4,z210,z103]),(0,[z1,z7,z371,z3,z4,z44])],[(0,[z1,z7,z3,z4,z5,z779]),(0,[z1,z70,z3,z4,z133,z52])],[(0,[z1,z63,z275,z3,z4,z5]),(0,[z1,z68,z3,z4,z133,z6]),(0,[z1,z7,z3,z4,z19,z6]),(0,[z7,z3,z4,z5,z780,z6])],[(0,[z1,z7,z4,z301,z19,z6])],[(0,[z196,z489,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z781]),(0,[z1,z3,z4,z5,z752,z6]),(0,[z1,z7,z3,z4,z212,z33])],[(0,[z1,z7,z3,z4,z5,z782]),(0,[z97,z7,z402,z3,z4,z30]),(0,[z1,z783,z3,z4,z5,z6]),(0,[z1,z206,z59,z4,z5,z6]),(0,[z1,z7,z3,z4,z91,z64]),(0,[z1,z84,z3,z5,z312,z85]),(0,[z1,z7,z3,z4,z784,z5])],[(0,[z25,z745,z3,z4,z5,z6]),(0,[z1,z785,z3,z4,z5,z6]),(0,[z215,z7,z3,z190,z5,z6]),(0,[z0,z275,z3,z4,z5,z9])],[(0,[z1,z7,z3,z4,z5,z786]),(0,[z1,z3,z4,z5,z52,z64])]],
   [[(0,[z1,z7,z3,z4,z5,z787]),(0,[z1,z7,z3,z788,z5,z6]),(0,[z1,z7,z3,z789,z4,z5]),(0,[z1,z7,z790,z3,z4,z6]),(0,[z1,z7,z791,z3,z4,z6]),(0,[z7,z3,z4,z5,z6,z792])],[(0,[z1,z7,z3,z4,z793,z6])],[(0,[z1,z7,z794,z4,z5,z6]),(0,[z1,z7,z3,z5,z6,z737])],[(0,[z1,z7,z3,z4,z5,z795]),(0,[z1,z7,z3,z4,z5,z66]),(0,[z1,z796,z3,z4,z5,z6])],[(0,[z47,z7,z74,z4,z48,z6])],[(0,[z47,z7,z315,z4,z5,z6]),(0,[z1,z797,z3,z4,z5,z6]),(0,[z1,z7,z191,z4,z141,z6]),(0,[z186,z7,z3,z4,z350,z6]),(0,[z1,z7,z798,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z799]),(0,[z1,z7,z3,z4,z800,z6]),(0,[z1,z7,z202,z12,z5,z6]),(0,[z801,z1,z3,z4,z5,z6])],[(0,[z377,z7,z245,z4,z5,z6]),(1,[z1,z3,z4,z752,z6]),(0,[z1,z3,z4,z210,z752,z6]),(0,[z1,z7,z3,z802,z5,z6])]],
   [[(0,[z1,z7,z803,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z804]),(0,[z1,z3,z735,z101,z5,z6]),(0,[z1,z7,z3,z4,z5,z805]),(0,[z1,z7,z806,z3,z4,z5]),(0,[z1,z7,z54,z198,z3,z4])],[(0,[z1,z7,z4,z5,z807,z6]),(0,[z1,z230,z808,z4,z5,z6]),(0,[z1,z7,z3,z4,z6,z809]),(0,[z1,z7,z3,z5,z719,z6])],[(0,[z1,z106,z3,z4,z133,z6]),(0,[z1,z7,z810,z3,z4,z6]),(0,[z47,z7,z74,z4,z5,z67]),(0,[z1,z302,z3,z4,z5,z53]),(0,[z1,z7,z197,z4,z712,z6])],[(0,[z1,z7,z95,z4,z5,z811])],[(0,[z215,z7,z3,z495,z5,z6]),(0,[z1,z7,z3,z4,z5,z812]),(0,[z180,z7,z3,z190,z5,z6]),(0,[z1,z70,z187,z3,z4,z5]),(0,[z1,z7,z3,z4,z813,z6]),(0,[z1,z7,z371,z3,z126,z4]),(0,[z1,z7,z3,z223,z5,z127])],[(0,[z1,z302,z3,z4,z5,z6]),(0,[z1,z7,z84,z3,z496,z5]),(0,[z1,z7,z3,z4,z43,z758])],[(0,[z1,z3,z4,z5,z6,z814])],[(0,[z1,z815,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z4,z301,z712,z6])],[],[(0,[z1,z7,z3,z816,z4,z6])],[(0,[z1,z7,z817,z3,z4,z5]),(0,[z1,z3,z4,z5,z6,z312]),(0,[z1,z3,z4,z210,z582,z6]),(0,[z1,z7,z3,z4,z719,z6])],[(0,[z1,z7,z818,z3,z4,z6]),(0,[z90,z1,z3,z735,z5,z6]),(0,[z1,z7,z3,z118,z719,z6])],[(0,[z819,z7,z3,z4,z5,z6]),(0,[z1,z7,z202,z802,z5,z6])],[(0,[z1,z62,z59,z4,z5,z6]),(0,[z820,z7,z3,z4,z5,z6]),(1,[z1,z3,z735,z5,z6]),(0,[z1,z821,z3,z4,z5,z6])],[(0,[z27,z7,z490,z4,z5,z6]),(0,[z1,z7,z4,z5,z6,z822])]],
   [[(0,[z1,z3,z4,z752,z169,z6])],[(0,[z1,z7,z3,z4,z5,z823]),(0,[z1,z702,z3,z4,z210,z6]),(0,[z1,z7,z3,z4,z182,z43])],[(0,[z1,z824,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z825,z6]),(0,[z1,z7,z826,z4,z5,z6]),(0,[z1,z7,z71,z3,z174,z41])],[(0,[z17,z7,z3,z4,z30,z6])],[(0,[z1,z7,z3,z4,z5,z827]),(0,[z1,z7,z3,z4,z5,z828])],[(0,[z1,z7,z3,z453,z48,z6]),(0,[z1,z172,z3,z4,z91,z6]),(0,[z1,z7,z3,z4,z5,z829]),(0,[z1,z7,z4,z5,z33,z764])],[(0,[z1,z7,z3,z115,z719,z6])],[(0,[z1,z830,z3,z4,z5,z6]),(0,[z1,z7,z831,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z832]),(0,[z1,z7,z3,z4,z5,z833]),(0,[z834,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z6,z135])]],
   [[(0,[z1,z7,z835,z4,z5,z6]),(0,[z1,z7,z836,z3,z4,z5]),(0,[z1,z7,z3,z4,z5,z837]),(0,[z77,z7,z3,z717,z5,z6]),(0,[z1,z7,z3,z4,z350,z232])],[(0,[z1,z7,z3,z4,z838,z6]),(0,[z1,z7,z3,z4,z839,z6]),(0,[z1,z7,z840,z4,z5,z6]),(0,[z1,z7,z3,z4,z841,z6]),(0,[z1,z7,z3,z4,z5,z842]),(0,[z1,z7,z3,z719,z41,z6])],[(0,[z209,z7,z3,z4,z5,z64]),(0,[z1,z172,z3,z4,z5,z6]),(0,[z1,z7,z478,z3,z41,z6])],[(0,[z1,z253,z59,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z843]),(0,[z1,z7,z844,z4,z5,z6]),(0,[z181,z7,z3,z4,z314,z5]),(0,[z1,z7,z4,z802,z5,z6]),(0,[z845,z7,z3,z4,z5,z6]),(0,[z1,z7,z198,z3,z151,z4])],[(0,[z1,z175,z3,z4,z5,z6]),(0,[z1,z846,z59,z4,z5,z6]),(0,[z1,z7,z3,z4,z91,z6])],[(0,[z1,z227,z59,z4,z5,z6]),(0,[z1,z7,z198,z3,z4,z99]),(0,[z335,z7,z3,z4,z5,z9]),(0,[z1,z7,z3,z4,z376,z43])],[(0,[z1,z7,z847,z4,z5,z6]),(0,[z1,z7,z3,z453,z5,z66]),(1,[z7,z3,z717,z5,z6]),(0,[z1,z7,z371,z3,z4,z53]),(0,[z1,z3,z4,z5,z52,z753])],[(0,[z1,z848,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z849,z9])]],
   [[(0,[z1,z7,z3,z4,z5,z850]),(0,[z1,z62,z846,z4,z5,z6]),(0,[z851,z1,z7,z3,z4,z5])],[(0,[z1,z489,z3,z4,z48,z6]),(0,[z1,z852,z3,z4,z5,z6]),(0,[z1,z7,z4,z301,z156,z6]),(0,[z219,z1,z23,z4,z5,z521]),(0,[z1,z7,z3,z4,z5,z853]),(0,[z90,z1,z3,z101,z5,z232]),(0,[z1,z7,z3,z4,z5,z753]),(0,[z1,z7,z371,z3,z4,z6])],[(0,[z1,z7,z3,z4,z5,z737]),(0,[z1,z7,z3,z4,z758,z44])],[],[(0,[z1,z68,z3,z4,z91,z6]),(0,[z1,z51,z3,z4,z5,z64]),(0,[z1,z7,z854,z4,z5,z6]),(0,[z1,z172,z3,z4,z5,z174]),(0,[z1,z3,z4,z6,z135,z312])],[(0,[z1,z7,z3,z4,z855,z6]),(0,[z1,z275,z3,z4,z5,z6]),(0,[z25,z7,z227,z4,z5,z6])],[(0,[z1,z7,z95,z453,z5,z6])],[(0,[z1,z489,z3,z4,z5,z67]),(0,[z1,z7,z191,z4,z116,z5])]],
   [[(0,[z856,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z857,z5,z6]),(0,[z858,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z405,z5,z127]),(0,[z1,z7,z198,z3,z4,z401])],[(0,[z1,z7,z3,z4,z5,z283])],[(0,[z1,z7,z3,z4,z5,z859]),(1,[z7,z710,z4,z5,z6]),(0,[z1,z860,z3,z4,z5,z6]),(0,[z1,z861,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z225]),(0,[z1,z7,z3,z4,z862,z6]),(0,[z1,z863,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z864,z6]),(0,[z1,z7,z3,z4,z5,z865]),(0,[z1,z7,z3,z4,z212,z52]),(0,[z1,z7,z3,z4,z5,z174])],[],[(0,[z1,z7,z227,z4,z5,z6]),(0,[z25,z68,z227,z4,z5,z6]),(0,[z1,z7,z3,z4,z866,z6]),(0,[z1,z867,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z868]),(0,[z1,z7,z3,z4,z210,z103])],[(0,[z120,z164,z106,z3,z4,z5]),(0,[z7,z245,z710,z4,z5,z6]),(0,[z1,z869,z3,z4,z5,z6]),(0,[z1,z870,z3,z4,z5,z6])],[(0,[z1,z7,z871,z4,z5,z6]),(0,[z7,z3,z190,z717,z5,z6]),(0,[z872,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z873]),(0,[z90,z1,z307,z101,z5,z6]),(1,[z1,z7,z3,z719,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z874]),(0,[z875,z7,z3,z4,z5,z6]),(0,[z1,z7,z371,z3,z4,z33])],[(0,[z90,z1,z3,z531,z5,z6]),(0,[z1,z7,z3,z4,z5,z876]),(0,[z1,z7,z3,z4,z6,z877])],[(0,[z1,z878,z3,z4,z5,z6]),(0,[z879,z7,z3,z4,z5,z6])],[(0,[z1,z7,z506,z69,z5,z6]),(0,[z1,z880,z3,z4,z5,z6]),(0,[z881,z7,z3,z4,z5,z6])],[(0,[z1,z106,z3,z4,z91,z6]),(0,[z215,z175,z3,z190,z5,z6]),(0,[z1,z7,z3,z882,z5,z6]),(0,[z1,z7,z3,z249,z118,z6]),(0,[z1,z7,z71,z3,z41,z406])],[(0,[z1,z7,z3,z4,z883,z6]),(0,[z1,z7,z3,z4,z780,z6]),(0,[z0,z7,z488,z3,z4,z5]),(0,[z219,z1,z23,z4,z5,z10]),(0,[z1,z7,z340,z4,z350,z6]),(0,[z1,z162,z3,z4,z210,z6]),(0,[z1,z162,z3,z4,z752,z6])],[(0,[z1,z7,z3,z884,z5,z6]),(0,[z186,z7,z3,z4,z91,z6]),(0,[z1,z7,z3,z4,z5,z885]),(1,[z1,z7,z4,z712,z6]),(0,[z1,z7,z71,z3,z290,z4])],[(0,[z1,z7,z3,z4,z886,z6]),(0,[z1,z7,z887,z3,z4,z6]),(0,[z1,z7,z191,z402,z4,z5]),(0,[z1,z888,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z198,z3,z4,z153])],[(0,[z97,z7,z191,z4,z30,z6]),(0,[z889,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z890,z6]),(0,[z1,z7,z3,z290,z4,z210])],[(0,[z339,z106,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z891]),(0,[z1,z7,z892,z4,z5,z6]),(1,[z1,z846,z4,z5,z6]),(0,[z1,z7,z893,z4,z5,z6])],[(0,[z186,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z894]),(0,[z1,z7,z3,z4,z43,z406])],[(0,[z25,z7,z3,z453,z5,z6]),(1,[z1,z7,z4,z5,z764]),(0,[z1,z7,z699,z4,z5,z33]),(0,[z1,z895,z3,z4,z5,z6]),(0,[z1,z3,z4,z896,z5,z6])],[(0,[z7,z106,z227,z4,z5,z6]),(0,[z47,z7,z74,z13,z5,z6]),(0,[z1,z7,z4,z5,z897,z6]),(0,[z1,z7,z307,z4,z5,z64]),(0,[z1,z7,z3,z4,z898,z6])],[(0,[z1,z270,z3,z4,z5,z6]),(0,[z1,z275,z3,z4,z5,z85]),(0,[z219,z1,z23,z4,z5,z6]),(0,[z219,z1,z846,z4,z5,z6]),(0,[z90,z1,z340,z101,z5,z6]),(0,[z1,z899,z3,z4,z5,z6]),(0,[z1,z302,z3,z4,z6,z135])],[(0,[z47,z7,z74,z4,z19,z6]),(0,[z1,z7,z3,z4,z900,z6]),(0,[z196,z7,z59,z4,z5,z6]),(0,[z1,z7,z901,z4,z5,z6]),(0,[z1,z7,z3,z4,z182,z502])]],
   [[(0,[z1,z7,z3,z4,z6,z758])],[(0,[z1,z745,z3,z4,z5,z6]),(0,[z209,z7,z3,z4,z5,z6]),(0,[z1,z7,z902,z3,z5,z6]),(0,[z1,z903,z3,z4,z5,z6]),(0,[z97,z7,z3,z4,z116,z30]),(0,[z1,z3,z4,z5,z904,z6]),(0,[z0,z1,z302,z3,z4,z5]),(0,[z1,z3,z107,z735,z5,z6])],[(0,[z1,z70,z275,z3,z4,z5])],[(0,[z186,z68,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z48,z67]),(0,[z1,z7,z3,z4,z905,z6]),(0,[z1,z906,z3,z4,z5,z6]),(0,[z215,z7,z3,z190,z5,z225]),(0,[z1,z7,z907,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z908])],[(0,[z1,z7,z909,z3,z4,z5]),(0,[z1,z7,z3,z453,z5,z6]),(0,[z1,z7,z59,z453,z5,z6]),(0,[z7,z3,z717,z26,z5,z6]),(0,[z1,z7,z3,z4,z5,z910]),(0,[z911,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z912,z6]),(0,[z1,z3,z107,z5,z443,z6]),(0,[z1,z7,z3,z4,z913,z6])],[(0,[z120,z106,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z914]),(0,[z1,z3,z4,z5,z174,z308])],[(0,[z209,z7,z3,z4,z350,z6]),(1,[z1,z7,z3,z5,z737])],[(0,[z1,z7,z3,z915,z4,z5]),(0,[z1,z7,z191,z4,z5,z6]),(0,[z1,z7,z3,z4,z916,z6]),(0,[z1,z7,z3,z4,z5,z917]),(0,[z1,z7,z3,z126,z5,z278])]],
   [[(0,[z25,z489,z3,z4,z5,z6]),(0,[z47,z7,z74,z4,z5,z66]),(0,[z1,z7,z3,z4,z5,z918]),(0,[z1,z51,z3,z4,z5,z53]),(0,[z1,z302,z371,z3,z4,z6])],[(0,[z1,z7,z69,z453,z5,z6]),(0,[z919,z7,z3,z4,z5,z6]),(0,[z1,z216,z3,z4,z169,z6]),(0,[z1,z7,z4,z5,z764,z6])],[(0,[z1,z920,z7,z3,z4,z5]),(0,[z1,z7,z921,z4,z5,z6]),(0,[z1,z3,z4,z5,z922,z6])],[(0,[z1,z51,z3,z4,z5,z753]),(0,[z1,z302,z3,z4,z5,z52]),(0,[z1,z7,z3,z4,z5,z923])],[(0,[z1,z7,z3,z4,z924,z5]),(0,[z1,z7,z3,z4,z925,z6]),(0,[z1,z7,z3,z4,z5,z926]),(0,[z1,z7,z340,z4,z5,z64]),(0,[z1,z7,z197,z4,z301,z6])],[(1,[z745,z3,z4,z5,z6]),(0,[z120,z745,z3,z4,z5,z6]),(0,[z1,z7,z927,z4,z5,z6]),(0,[z90,z186,z3,z101,z5,z6])],[(0,[z523,z7,z3,z26,z5,z6])],[(0,[z1,z7,z928,z4,z5,z6]),(0,[z196,z219,z23,z4,z5,z6])]],
   [[(0,[z1,z489,z3,z4,z5,z6]),(0,[z120,z63,z106,z3,z4,z5]),(0,[z1,z489,z59,z4,z5,z6]),(0,[z47,z7,z56,z4,z5,z6]),(0,[z1,z275,z3,z4,z5,z127]),(0,[z1,z3,z4,z735,z5,z6]),(0,[z1,z929,z3,z4,z5,z6]),(0,[z1,z7,z3,z126,z5,z127])],[(0,[z1,z229,z3,z453,z5,z6]),(0,[z1,z7,z930,z4,z5,z6]),(0,[z1,z931,z3,z4,z5,z6]),(0,[z196,z7,z23,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z390]),(0,[z1,z7,z602,z4,z5,z139]),(0,[z1,z7,z3,z4,z932,z5])],[(0,[z1,z933,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z934]),(0,[z7,z3,z4,z76,z780,z6]),(0,[z935,z7,z3,z4,z5,z6])],[(0,[z186,z106,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z936,z6])],[(0,[z7,z106,z3,z453,z5,z6]),(0,[z27,z7,z641,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z937])],[(0,[z1,z7,z938,z4,z5,z6]),(0,[z97,z98,z3,z4,z30,z6]),(0,[z1,z7,z3,z4,z5,z330]),(0,[z1,z7,z3,z5,z737,z85])],[(0,[z1,z7,z23,z453,z5,z6]),(0,[z1,z7,z3,z939,z4,z5]),(0,[z1,z7,z3,z4,z940,z6]),(0,[z1,z7,z3,z4,z5,z232]),(0,[z1,z7,z941,z4,z5,z6]),(0,[z1,z7,z138,z4,z5,z139])],[(0,[z1,z7,z3,z4,z5,z942]),(0,[z97,z7,z3,z4,z780,z6]),(0,[z1,z943,z3,z4,z5,z6]),(0,[z1,z7,z4,z712,z5,z6]),(0,[z1,z302,z3,z4,z5,z33]),(0,[z1,z7,z3,z290,z115,z4])]],
   [[(0,[z47,z106,z59,z4,z5,z6]),(0,[z1,z7,z3,z453,z19,z6])],[(0,[z1,z68,z3,z4,z5,z390]),(0,[z1,z944,z3,z4,z5,z6]),(0,[z1,z945,z7,z3,z4,z5]),(0,[z1,z7,z946,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z947])],[(0,[z1,z7,z808,z4,z5,z6]),(0,[z29,z7,z3,z4,z780,z6])],[(0,[z1,z7,z508,z4,z5,z6]),(0,[z25,z68,z508,z4,z5,z6]),(0,[z1,z7,z191,z4,z19,z6]),(0,[z1,z7,z3,z4,z5,z948]),(0,[z1,z7,z3,z4,z949,z5]),(0,[z181,z543,z7,z3,z4,z5])],[(0,[z1,z7,z3,z4,z950,z6]),(0,[z951,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z952]),(0,[z1,z3,z107,z5,z6,z664]),(0,[z1,z3,z4,z5,z6,z953])],[(0,[z1,z7,z3,z954,z5,z6]),(0,[z1,z23,z846,z4,z5,z6]),(0,[z1,z3,z4,z5,z52,z250]),(0,[z1,z7,z955,z3,z5,z6]),(0,[z1,z465,z3,z4,z5,z53]),(0,[z1,z956,z3,z4,z5,z6]),(0,[z1,z71,z3,z308,z41,z6]),(0,[z1,z7,z3,z4,z5,z758])],[(0,[z1,z846,z3,z4,z5,z6]),(0,[z1,z957,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z958,z6]),(0,[z1,z7,z3,z4,z5,z959]),(0,[z1,z7,z198,z3,z4,z258]),(0,[z1,z7,z3,z4,z5,z203])],[(0,[z571,z7,z3,z26,z5,z6]),(0,[z1,z7,z3,z4,z5,z960])],[(0,[z1,z489,z3,z13,z5,z6]),(0,[z1,z489,z23,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z9]),(0,[z1,z7,z3,z4,z5,z961]),(0,[z1,z32,z7,z4,z5,z764]),(0,[z1,z7,z962,z3,z4,z5])],[(0,[z1,z963,z3,z4,z5,z6]),(0,[z1,z7,z198,z3,z4,z266]),(0,[z1,z7,z3,z4,z6,z964])],[(0,[z1,z489,z3,z4,z19,z6]),(0,[z1,z7,z95,z4,z5,z965]),(0,[z1,z7,z3,z4,z5,z811]),(0,[z1,z7,z307,z4,z5,z6]),(0,[z1,z673,z3,z4,z5,z52]),(0,[z1,z7,z213,z3,z5,z85])],[(0,[z1,z162,z3,z4,z210,z390]),(0,[z1,z7,z138,z4,z5,z764])],[(0,[z1,z7,z3,z4,z5,z966]),(0,[z1,z7,z3,z4,z5,z967]),(0,[z1,z7,z3,z968,z5,z6])],[(0,[z1,z7,z3,z4,z969,z6]),(0,[z0,z55,z7,z3,z4,z5]),(0,[z1,z7,z371,z3,z4,z52])]],
   [[(0,[z1,z7,z3,z4,z5,z970]),(0,[z1,z971,z3,z4,z5,z6])],[(0,[z1,z106,z3,z4,z5,z390]),(0,[z1,z7,z402,z4,z493,z5]),(0,[z1,z7,z307,z4,z350,z6]),(0,[z1,z7,z3,z126,z5,z737])],[(0,[z1,z7,z3,z4,z5,z972])],[(0,[z90,z1,z3,z101,z350,z6]),(0,[z1,z172,z3,z4,z210,z6])],[(0,[z1,z7,z3,z4,z973,z6]),(0,[z583,z106,z3,z4,z5,z6]),(0,[z1,z7,z974,z3,z5,z6])],[(0,[z1,z7,z4,z975,z5,z6]),(0,[z1,z489,z3,z4,z5,z66]),(0,[z1,z7,z3,z976,z5,z6]),(0,[z1,z7,z4,z116,z493,z5]),(0,[z1,z7,z3,z4,z5,z977])],[(0,[z47,z7,z74,z4,z5,z6])],[]],
   [[(0,[z1,z7,z3,z4,z978,z6]),(0,[z1,z7,z3,z979,z5,z6]),(0,[z1,z7,z4,z5,z980,z6]),(0,[z1,z7,z3,z981,z5,z6])],[(0,[z1,z63,z3,z107,z4,z5]),(0,[z1,z7,z3,z4,z982,z5]),(0,[z1,z7,z3,z4,z5,z849])],[(0,[z1,z7,z3,z4,z5,z67]),(0,[z1,z7,z3,z4,z5,z983]),(0,[z1,z7,z984,z4,z5,z6]),(0,[z1,z7,z402,z3,z4,z5]),(0,[z181,z7,z3,z4,z5,z849]),(0,[z1,z7,z3,z4,z752,z6])],[(0,[z1,z7,z340,z4,z5,z6]),(0,[z1,z7,z985,z4,z5,z6]),(0,[z90,z1,z3,z688,z5,z6])],[(0,[z1,z7,z986,z3,z4,z5]),(0,[z1,z7,z987,z4,z5,z6]),(0,[z1,z567,z59,z4,z5,z6]),(0,[z1,z988,z3,z4,z5,z6]),(0,[z0,z7,z3,z4,z5,z849]),(0,[z989,z7,z3,z4,z5,z6]),(0,[z1,z172,z3,z290,z4,z5])],[],[(0,[z1,z990,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z991]),(0,[z1,z7,z191,z4,z301,z6]),(0,[z1,z7,z3,z4,z5,z992]),(0,[z1,z172,z71,z3,z41,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z993]),(0,[z1,z7,z3,z192,z5,z127]),(0,[z994,z7,z3,z4,z5,z6])],[(0,[z1,z229,z3,z4,z48,z6]),(0,[z1,z7,z3,z4,z350,z64]),(0,[z1,z7,z3,z995,z5,z6])],[(0,[z1,z7,z3,z996,z5,z6]),(0,[z47,z7,z299,z4,z5,z6]),(0,[z1,z7,z71,z3,z41,z72]),(0,[z1,z997,z3,z4,z5,z6])],[(0,[z219,z1,z227,z4,z5,z6]),(0,[z1,z68,z340,z4,z5,z6]),(0,[z47,z229,z74,z4,z5,z6]),(0,[z1,z998,z3,z4,z5,z6]),(0,[z1,z7,z3,z115,z118,z6]),(0,[z1,z7,z3,z290,z4,z5])],[(0,[z1,z7,z3,z4,z5,z999])],[(0,[z1,z7,z3,z4,z1000,z6]),(0,[z25,z230,z3,z4,z5,z6]),(0,[z27,z7,z710,z4,z5,z6]),(0,[z1001,z7,z3,z4,z5,z6]),(0,[z1,z7,z28,z4,z712,z6])],[(0,[z1,z7,z3,z13,z48,z6]),(0,[z1,z7,z3,z4,z5,z1002]),(0,[z1,z7,z71,z3,z41,z6])],[(0,[z1,z229,z3,z4,z5,z67]),(0,[z209,z7,z3,z4,z91,z6]),(0,[z1,z7,z3,z4,z212,z139]),(0,[z1003,z7,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z6,z1004])]],
   [[(0,[z1,z1005,z3,z4,z5,z6]),(0,[z47,z7,z710,z4,z5,z6]),(0,[z1,z7,z202,z12,z5,z203]),(0,[z1,z7,z197,z4,z301,z330])],[(0,[z1,z7,z1006,z3,z5,z6]),(0,[z1,z7,z3,z735,z5,z6]),(0,[z1,z7,z84,z371,z3,z4])],[(0,[z196,z7,z3,z4,z5,z6]),(0,[z1,z7,z1007,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z965]),(0,[z181,z1,z302,z3,z4,z5]),(0,[z90,z1,z3,z101,z5,z64]),(0,[z1,z7,z3,z4,z1008,z6])],[(0,[z1,z7,z3,z1009,z5,z6]),(0,[z1,z7,z3,z4,z5,z1010]),(0,[z1,z7,z3,z4,z1011,z5]),(0,[z1,z7,z1012,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z1013]),(0,[z1,z7,z3,z13,z5,z67]),(0,[z1,z1014,z3,z4,z5,z6]),(1,[z7,z3,z4,z780,z6]),(0,[z1,z7,z3,z4,z1015,z6]),(0,[z1,z7,z3,z4,z182,z457])],[(0,[z1,z230,z3,z4,z5,z6]),(0,[z489,z106,z3,z4,z5,z6]),(0,[z1,z7,z1016,z3,z4,z6]),(0,[z1,z7,z1017,z4,z5,z6]),(0,[z1,z3,z4,z5,z1018,z6])],[(0,[z1,z7,z3,z4,z19,z67]),(0,[z1,z7,z3,z4,z1019,z6]),(0,[z1,z7,z3,z4,z5,z1020]),(0,[z1021,z7,z3,z4,z5,z6])],[(0,[z97,z7,z4,z493,z30,z6]),(0,[z1,z216,z3,z4,z91,z6]),(0,[z1,z7,z3,z4,z5,z764]),(0,[z1,z7,z1022,z4,z5,z6])]],
   [[(0,[z1,z7,z4,z5,z6,z1023]),(0,[z1,z7,z1024,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1025]),(0,[z1,z7,z3,z4,z182,z427])],[(0,[z1,z7,z1026,z3,z4,z6]),(0,[z1,z7,z3,z4,z48,z66]),(0,[z1,z7,z1027,z4,z5,z6]),(0,[z1028,z7,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1029])],[(0,[z1,z7,z3,z4,z5,z1030]),(0,[z196,z68,z3,z4,z5,z6]),(0,[z29,z7,z3,z4,z76,z6]),(0,[z1,z7,z653,z4,z301,z6]),(0,[z181,z7,z3,z4,z5,z526]),(0,[z1,z7,z4,z1031,z5,z6])],[(0,[z1,z106,z340,z4,z5,z6]),(0,[z1,z7,z3,z1032,z4,z5])],[],[(0,[z1,z162,z3,z4,z485,z6]),(0,[z186,z7,z340,z4,z5,z6])],[(0,[z477,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z1033,z5,z6])],[(0,[z82,z106,z3,z4,z5,z6]),(0,[z1,z63,z3,z4,z5,z53]),(0,[z1,z7,z1034,z3,z4,z5]),(0,[z1,z7,z95,z12,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z1035]),(0,[z1,z7,z28,z4,z141,z6])],[(0,[z1,z1036,z3,z4,z5,z6]),(0,[z1,z7,z1037,z4,z5,z6]),(0,[z1,z7,z84,z371,z3,z85])],[(0,[z369,z68,z3,z4,z5,z6]),(0,[z27,z7,z245,z4,z5,z6])],[(0,[z323,z68,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1038]),(0,[z1,z7,z470,z12,z5,z6])],[(0,[z7,z3,z4,z5,z849,z6]),(0,[z1,z7,z3,z4,z5,z1039]),(0,[z1,z7,z3,z4,z91,z232]),(0,[z1,z7,z3,z4,z5,z406]),(0,[z1,z7,z84,z3,z5,z737])],[(0,[z1,z7,z202,z453,z5,z6]),(0,[z1,z7,z4,z493,z5,z6]),(0,[z1,z548,z3,z4,z5,z52])],[(0,[z7,z3,z4,z717,z5,z6]),(0,[z1,z371,z3,z4,z6,z312])],[(0,[z1,z7,z197,z4,z301,z283])]],
   [[(0,[z1,z7,z3,z4,z5,z1040]),(0,[z1,z7,z3,z1041,z5,z6])],[(0,[z1,z7,z3,z4,z5,z1042]),(0,[z1,z7,z1043,z4,z5,z6]),(0,[z1,z70,z3,z4,z5,z238])],[(0,[z196,z106,z3,z4,z5,z6]),(0,[z1,z7,z3,z5,z6,z1044]),(0,[z1,z1045,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z1046,z6]),(0,[z1,z7,z71,z3,z290,z41])],[],[(0,[z1,z7,z3,z4,z5,z1047]),(0,[z1,z7,z3,z4,z1048,z6]),(0,[z1,z7,z3,z4,z1049,z5]),(0,[z1,z1050,z7,z3,z4,z5]),(0,[z1051,z7,z3,z4,z5,z6]),(0,[z1,z1052,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z1053]),(0,[z1,z7,z3,z4,z5,z1054]),(0,[z77,z7,z95,z26,z5,z6]),(0,[z215,z230,z3,z190,z5,z6]),(0,[z1,z7,z4,z1055,z5,z6]),(0,[z1,z7,z1056,z4,z5,z6])],[(0,[z1,z275,z198,z3,z4,z5]),(0,[z1,z7,z198,z3,z4,z758])],[(0,[z1,z7,z3,z1057,z5,z6]),(0,[z1,z489,z227,z4,z5,z6]),(0,[z186,z230,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1058]),(0,[z1,z302,z3,z4,z5,z139])]],
   [[(0,[z1,z1059,z3,z4,z5,z6])],[(0,[z77,z7,z96,z26,z5,z6]),(0,[z1060,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1061])],[(0,[z1,z7,z3,z580,z5,z85]),(0,[z181,z1,z7,z371,z3,z4]),(0,[z1,z7,z307,z4,z91,z6]),(0,[z1,z399,z3,z4,z169,z6])],[(0,[z1,z7,z1062,z4,z5,z6]),(0,[z1,z7,z3,z4,z1063,z6])],[(0,[z90,z1,z63,z3,z4,z5]),(0,[z1,z7,z3,z1064,z5,z6]),(0,[z0,z1,z7,z371,z3,z4]),(0,[z219,z477,z23,z4,z5,z6]),(0,[z1065,z7,z3,z4,z5,z6]),(0,[z1,z7,z240,z4,z5,z33]),(0,[z1,z7,z802,z12,z5,z6])],[(0,[z1,z63,z7,z3,z4,z5]),(0,[z7,z3,z4,z780,z30,z6]),(0,[z625,z7,z3,z4,z76,z6]),(0,[z1066,z7,z3,z4,z5,z6])],[(0,[z1,z98,z3,z4,z5,z6])],[(0,[z1,z7,z1067,z4,z5,z6]),(0,[z1,z7,z22,z442,z5,z6]),(0,[z1,z7,z1068,z4,z5,z6])]],
   [[(0,[z303,z106,z3,z4,z5,z6]),(0,[z1,z7,z227,z4,z5,z1047]),(0,[z1,z7,z3,z4,z1069,z6]),(0,[z1,z7,z222,z4,z5,z33])],[(0,[z90,z1,z3,z101,z5,z6]),(0,[z1,z3,z4,z210,z91,z6]),(0,[z1,z7,z198,z3,z4,z446])],[(0,[z1,z7,z3,z4,z5,z1070]),(0,[z1,z1071,z7,z3,z4,z5]),(0,[z1,z7,z3,z4,z5,z1072]),(0,[z1,z7,z618,z4,z5,z139]),(0,[z1073,z1,z7,z4,z5,z6])],[(0,[z1,z7,z1074,z4,z5,z6]),(0,[z1,z7,z28,z4,z19,z6]),(0,[z1,z51,z275,z3,z4,z5]),(0,[z1,z7,z1075,z3,z4,z6])],[(0,[z1076,z7,z3,z4,z5,z6]),(0,[z1,z7,z84,z3,z5,z85])],[(0,[z1,z7,z846,z4,z5,z6])],[(0,[z1,z1077,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z753])],[(0,[z1,z7,z3,z4,z1078,z6]),(0,[z1,z7,z3,z4,z48,z6]),(0,[z0,z7,z3,z4,z5,z9]),(0,[z1,z1079,z3,z4,z5,z6]),(0,[z1,z7,z54,z3,z5,z85])]],
   [[(0,[z1,z7,z3,z4,z5,z1080])],[(0,[z1,z7,z340,z4,z91,z6])],[(0,[z109,z106,z3,z4,z5,z6]),(0,[z1,z673,z3,z4,z210,z6]),(0,[z1,z3,z290,z4,z5,z308])],[(0,[z1,z7,z3,z4,z5,z1081]),(0,[z1,z230,z928,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1082]),(0,[z186,z7,z3,z4,z5,z232])],[(0,[z1,z1083,z7,z3,z4,z5]),(0,[z7,z3,z4,z5,z8,z849]),(0,[z1084,z7,z3,z4,z5,z6])],[(0,[z1,z1085,z3,z4,z5,z6])],[(0,[z1,z489,z3,z453,z5,z6])],[(0,[z1,z7,z227,z4,z5,z970]),(0,[z1,z70,z3,z4,z5,z634]),(0,[z1,z7,z3,z4,z5,z1086]),(0,[z90,z209,z3,z101,z5,z6]),(0,[z1,z7,z3,z4,z5,z64]),(0,[z1,z7,z3,z1087,z4,z5])]],
   [[(0,[z25,z7,z95,z4,z5,z6]),(0,[z1,z7,z1088,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1089]),(0,[z1,z7,z1090,z4,z5,z6]),(0,[z1,z7,z3,z11,z5,z127]),(0,[z1,z7,z3,z4,z5,z1091])],[(0,[z1,z1092,z3,z4,z5,z6]),(0,[z0,z7,z3,z4,z5,z119]),(0,[z209,z7,z3,z4,z5,z232]),(0,[z1,z1093,z3,z4,z5,z6])],[(0,[z1,z229,z3,z13,z5,z6]),(0,[z1,z7,z3,z4,z182,z60]),(0,[z1,z7,z3,z4,z5,z1094])],[(0,[z77,z7,z3,z26,z5,z6]),(0,[z1,z7,z371,z3,z4,z139])],[(0,[z1,z229,z3,z4,z19,z6]),(0,[z1,z7,z3,z4,z1095,z6]),(0,[z1,z1096,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1097]),(0,[z1,z1098,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z1099,z6])],[(0,[z1,z7,z3,z4,z116,z5])],[(0,[z1,z68,z3,z4,z5,z64]),(0,[z1,z7,z3,z1100,z4,z5]),(0,[z1,z7,z3,z4,z1101,z5])]],
   [[(0,[z1,z7,z95,z4,z5,z6]),(0,[z1,z7,z1102,z3,z4,z5]),(1,[z7,z3,z4,z5,z849])],[(0,[z1,z7,z3,z13,z19,z6]),(0,[z1,z7,z3,z4,z5,z1103]),(0,[z1,z7,z3,z4,z5,z521]),(0,[z186,z7,z307,z4,z5,z6]),(0,[z1,z1104,z7,z3,z4,z5])],[(0,[z745,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1105]),(0,[z1,z7,z3,z4,z5,z1106]),(0,[z1,z7,z3,z4,z1107,z6])],[(0,[z1,z1108,z3,z4,z5,z6])],[(0,[z1,z7,z96,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z346]),(0,[z1,z7,z3,z4,z712,z6])],[(0,[z1,z7,z1109,z4,z5,z6]),(0,[z1,z229,z3,z4,z5,z66]),(0,[z1,z7,z3,z1110,z5,z6]),(1,[z1,z7,z3,z4,z758])],[(0,[z1,z164,z7,z3,z4,z5]),(0,[z1,z7,z3,z4,z5,z1111])],[(0,[z1,z1112,z3,z4,z5,z6]),(0,[z1113,z7,z3,z4,z5,z6]),(0,[z209,z7,z307,z4,z5,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 544) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 544).take 537) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1081)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [544, 537] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 145).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 145).take 111).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [145, 111] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_38907

theorem PEqualNP.Outside.L_meta_38907 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4209696960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4209696960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38907.solve