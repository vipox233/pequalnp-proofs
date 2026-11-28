import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43984

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
  Nat.testBit (4276813544 * 2 ^ 32 + 4276799624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0030186c04261501#64 ++ 0x400030186c042615#64 ++ 0x09f038fc0c7e3f77#64 ++ 0xb809f038fc0c7e3f#64 : BitVec 256),
   (0x1280c3103190ea24#64 ++ 0x801280c3103190ea#64 ++ 0x3681c7187393ffff#64 ++ 0x7a3681c7187393ff#64 : BitVec 256),
   (0x451605a582e34c49#64 ++ 0x01451605a582e34c#64 ++ 0xc71e07e783e3ccee#64 ++ 0xedc71e07e783e3cc#64 : BitVec 256),
   (0xa81b6806dc03b08e#64 ++ 0x02a81b6806dc03b0#64 ++ 0xf81ff807fc03f0dd#64 ++ 0xf7f81ff807fc03f0#64 : BitVec 256),
   (0xffc000036b5800f0#64 ++ 0x08ffc000036b5800#64 ++ 0xffe00007fffc00c3#64 ++ 0xf9ffe00007fffc00#64 : BitVec 256),
   (0xffedb6d800000000#64 ++ 0x04ffedb6d8000000#64 ++ 0xfffffff80000003f#64 ++ 0xe6fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [8, 6]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0030186c04261501 0x400030186c042615 0x09f038fc0c7e3f77 0xb809f038fc0c7e3f

def z1 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3681c7187393ffff 0x7a3681c7187393ff

def z2 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e3ccee 0xedc71e07e783e3cc

def z3 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf81ff807fc03f0dd 0xf7f81ff807fc03f0

def z4 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xffe00007fffc00c3 0xf9ffe00007fffc00

def z5 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xffe0001ffffe3ff7 0xf9ffe0001ffffe3f

def z6 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffff80000003f 0xe6fffffff8000000

def z7 : W := mkw 0xed6d34c800000000 0x04ed6d34c8000000 0xc97e38e000000000 0x84c97e38e0000000

def z8 : W := mkw 0xffedf7d83190ea24 0x84ffedf7d83190ea 0xfffffff87393ffff 0xfefffffff87393ff

def z9 : W := mkw 0x4500000102400040 0x0045000001024000 0xc700000783e000c2 0xe9c700000783e000

def z10 : W := mkw 0xbac00002691800b0 0x08bac00002691800 0x38e000007c1c0001 0x1038e000007c1c00

def z11 : W := mkw 0x001248049403b00e 0x02001248049403b0 0x000000000003f000 0x00000000000003f0

def z12 : W := mkw 0x57e496d800000000 0x0457e496d8000000 0x07e007f800000022 0x0007e007f8000000

def z13 : W := mkw 0xbae9fa5a5c00b086 0x06bae9fa5a5c00b0 0x38e1f8187c003011 0x1238e1f8187c0030

def z14 : W := mkw 0x0030186c04261501 0x400030186c042615 0x001038fc0c7e3f74 0x18001038fc0c7e3f

def z15 : W := mkw 0xa80968025c00b086 0x02a80968025c00b0 0x3801f8007c03f0dd 0x723801f8007c03f0

def z16 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xc81ff8078c03f01c 0x87c81ff8078c03f0

def z17 : W := mkw 0xed6d34cb4a4800d0 0x0ced6d34cb4a4800 0xc97e38e78c6c0000 0x85c97e38e78c6c00

def z18 : W := mkw 0x0000010000804800 0x0000000100008048 0x068007180393ffff 0x78068007180393ff

def z19 : W := mkw 0x0020104800000000 0x0000201048000000 0x09f038f800000037 0xa009f038f8000000

def z20 : W := mkw 0xfffdbefc04261501 0x44fffdbefc042615 0xfffffffc0c7e3f7f 0xfefffffffc0c7e3f

def z21 : W := mkw 0x0030186c04261501 0x400030186c042615 0x09f038fc0c7c0f22 0x8809f038fc0c7c0f

def z22 : W := mkw 0x452db6d800000000 0x04452db6d8000000 0xc71ffff80000003e 0xe6c71ffff8000000

def z23 : W := mkw 0xed1f6c86dc03b08e 0x02ed1f6c86dc03b0 0xff1fffe7fc03f0ff 0xf7ff1fffe7fc03f0

def z24 : W := mkw 0x450000036b5800f0 0x08450000036b5800 0xc7000007fffc00c2 0xf9c7000007fffc00

def z25 : W := mkw 0x0030186c04261501 0x400030186c042615 0x097038e40c6c0000 0x80097038e40c6c00

def z26 : W := mkw 0x12b0db7c35b6ff25 0xc012b0db7c35b6ff 0x3ff1fffc7fffffff 0xfa3ff1fffc7fffff

def z27 : W := mkw 0xbabbfb7efdb7ffaf 0xc2babbfb7efdb7ff 0xffffffffffffffff 0xffffffffffffffff

def z28 : W := mkw 0x1280000021100020 0x0012800000211000 0x3600000073800080 0x4036000000738000

def z29 : W := mkw 0x0010080404021000 0x0000100804040210 0x081038040c023055 0xb0081038040c0230

def z30 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xfffffffffffc00ff 0xfffffffffffffc00

def z31 : W := mkw 0x57c0000123580070 0x0857c00001235800 0x0fe000040ffc0043 0xb80fe000040ffc00

def z32 : W := mkw 0x1280831021904a20 0x801280831021904a 0x0680071803900f22 0x080680071803900f

def z33 : W := mkw 0xa81b2806cc03108a 0x02a81b2806cc0310 0xc81e38078c000000 0x85c81e38078c0000

def z34 : W := mkw 0x12adb6d800000000 0x0412adb6d8000000 0x369ffff80000003f 0x66369ffff8000000

def z35 : W := mkw 0xffe9b25b6b5800f0 0x0cffe9b25b6b5800 0xffe1f81ffffc00d3 0xfbffe1f81ffffc00

def z36 : W := mkw 0x002db6d800000000 0x04002db6d8000000 0x001ffff80000003c 0x06001ffff8000000

def z37 : W := mkw 0xffd605a7ebfb4cf9 0x09ffd605a7ebfb4c 0xf71e07e7f3e3ccee 0xedf71e07e7f3e3cc

def z38 : W := mkw 0xffcda69000000000 0x04ffcda690000000 0xf60fc70000000008 0x46f60fc700000000

def z39 : W := mkw 0xffd008276f7e15f1 0x48ffd008276f7e15 0xffe00007fffe3fc3 0xf9ffe00007fffe3f

def z40 : W := mkw 0xbac00002691800b0 0x08bac00002691800 0x3000000070000000 0x0030000000700000

def z41 : W := mkw 0x1280c2103110a224 0x801280c2103110a2 0x3081c01870103311 0x123081c018701033

def z42 : W := mkw 0x451604a582630449 0x01451604a5826304 0xc11e00e780600000 0x85c11e00e7806000

def z43 : W := mkw 0xba9beb16fd93faae 0x82ba9beb16fd93fa 0xfe9fff1fff93ffff 0xfffe9fff1fff93ff

def z44 : W := mkw 0x001605a480a34c09 0x01001605a480a34c 0x001e07e00003cc2c 0x04001e07e00003cc

def z45 : W := mkw 0x0000000123580070 0x0800000001235800 0x0000000003fc0000 0x080000000003fc00

def z46 : W := mkw 0x0020184804041100 0x4000201848040411 0x086038000c0c0000 0x00086038000c0c00

def z47 : W := mkw 0x5786c791b3d1ea6c 0x815786c791b3d1ea 0xf68fc71bf393ffff 0x7ff68fc71bf393ff

def z48 : W := mkw 0x000041003190ea24 0x80000041003190ea 0x000000007393ffc0 0x18000000007393ff

def z49 : W := mkw 0xbaedb6d800000000 0x04baedb6d8000000 0x38fffff80000003d 0x0638fffff8000000

def z50 : W := mkw 0x4504048000000000 0x0045040480000000 0xc71e07e00000002e 0xe4c71e07e0000000

def z51 : W := mkw 0xffffb7fd82e34c49 0x05ffffb7fd82e34c 0xffffffff83e3ccff 0xefffffffff83e3cc

def z52 : W := mkw 0xffc9200000000000 0x00ffc92000000000 0xfffff8000000001f 0xe6fffff800000000

def z53 : W := mkw 0x1280831021904a20 0x801280831021904a 0x3681c71803900f3f 0x6a3681c71803900f

def z54 : W := mkw 0x1280c2103110a224 0x801280c2103110a2 0x3681c018739033d3 0x7a3681c018739033

def z55 : W := mkw 0xffe496db6b5800f0 0x0cffe496db6b5800 0xffe007fffffc00e3 0xf9ffe007fffffc00

def z56 : W := mkw 0xa80b6002d801a08e 0x02a80b6002d801a0 0xf81ff803f001c09d 0xe7f81ff803f001c0

def z57 : W := mkw 0xa809200000000000 0x00a8092000000000 0xf81ff8000000001d 0xe6f81ff800000000

def z58 : W := mkw 0xffd605a7ebfb4cf9 0x09ffd605a7ebfb4c 0xfffe07e7ffffccef 0xfdfffe07e7ffffcc

def z59 : W := mkw 0x1292cb16fd93faae 0x821292cb16fd93fa 0x3681c71fff93ffff 0x7b3681c71fff93ff

def z60 : W := mkw 0x12a0da583514b324 0xc012a0da583514b3 0x38e1f8187c1c3311 0x1238e1f8187c1c33

def z61 : W := mkw 0x0000010000804800 0x0000000100008048 0x060007000383ccee 0x68060007000383cc

def z62 : W := mkw 0x5796c7b5b3f3ee6d 0x815796c7b5b3f3ee 0xf79fc7fff3f3ffff 0xfff79fc7fff3f3ff

def z63 : W := mkw 0xba89ea127d10b2a6 0x82ba89ea127d10b2 0x3881f8187c103311 0x123881f8187c1033

def z64 : W := mkw 0xffc4048000000000 0x00ffc40480000000 0xfffe07e00000002f 0xe4fffe07e0000000

def z65 : W := mkw 0xffc0000000000000 0x00ffc00000000000 0xffe0000000000003 0xe0ffe00000000000

def z66 : W := mkw 0x1280821000000000 0x0012808210000000 0x3601c70000000008 0x423601c700000000

def z67 : W := mkw 0x0000010000804800 0x0000000100008048 0x000000000383ccc0 0x08000000000383cc

def z68 : W := mkw 0xffedf6d81000a004 0x04ffedf6d81000a0 0xfffffff87003f0ff 0xf6fffffff87003f0

def z69 : W := mkw 0x00124806dc03b08e 0x0200124806dc03b0 0x00000007fc03f0c0 0x1100000007fc03f0

def z70 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xff7fffe000000008 0xc6ff7fffe0000000

def z71 : W := mkw 0x4500000102400040 0x0045000001024000 0xcfe000078ffc00c3 0xf9cfe000078ffc00

def z72 : W := mkw 0x0000000000000000 0x0000000000000000 0x09e000040c7c0043 0xb809e000040c7c00

def z73 : W := mkw 0x0030186c04261501 0x400030186c042615 0x001038f800023f34 0x00001038f800023f

def z74 : W := mkw 0x0012000480030008 0x0000120004800300 0xc01e00078003c0cc 0xe5c01e00078003c0

def z75 : W := mkw 0xed1f6da7dee3fccf 0x03ed1f6da7dee3fc 0xff1fffe7ffe3fcff 0xffff1fffe7ffe3fc

def z76 : W := mkw 0xa839386c04261501 0x40a839386c042615 0xf9fff8fc0c7e3f7f 0xfef9fff8fc0c7e3f

def z77 : W := mkw 0x0020106800240501 0x4000201068002405 0x01e000f8007c0f22 0x0801e000f8007c0f

def z78 : W := mkw 0xa80b6002d801a08e 0x02a80b6002d801a0 0xf00fc003f001c088 0x47f00fc003f001c0

def z79 : W := mkw 0x0000000000000000 0x0000000000000000 0x09e0001c0c7e3f77 0xb809e0001c0c7e3f

def z80 : W := mkw 0x001b68049403b00e 0x02001b68049403b0 0x001ff8000003f01c 0x06001ff8000003f0

def z81 : W := mkw 0xffc920036b5800f0 0x08ffc920036b5800 0xfffff807fffc00df 0xfffffff807fffc00

def z82 : W := mkw 0x0009200000000000 0x0000092000000000 0x001ff8000000001c 0x06001ff800000000

def z83 : W := mkw 0x000da69000000000 0x04000da690000000 0x000fc70000000008 0x06000fc700000000

def z84 : W := mkw 0x0010082404261501 0x4000100824042615 0x000000040c7e3f40 0x18000000040c7e3f

def z85 : W := mkw 0x1280000021100020 0x0012800000211000 0x3080000070100001 0x1030800000701000

def z86 : W := mkw 0x0010002400220401 0x0000100024002204 0x09f000e40c7e0c67 0xb809f000e40c7e0c

def z87 : W := mkw 0xffd24807ff5bb0fe 0x0affd24807ff5bb0 0xffe00007fffff0c3 0xf9ffe00007fffff0

def z88 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf89ff81ffc13ffff 0xfff89ff81ffc13ff

def z89 : W := mkw 0xffffbffd86e75d49 0x45ffffbffd86e75d 0xffffffff8fffffff 0xffffffffff8fffff

def z90 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3681c7007391c0cb 0x7a3681c7007391c0

def z91 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000003c0cc 0x60000000000003c0

def z92 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xf9e00007fc7c0001 0x91f9e00007fc7c00

def z93 : W := mkw 0xfffffededc03b08e 0x06fffffededc03b0 0xfffffffffc03f0ff 0xf7fffffffffc03f0

def z94 : W := mkw 0xffc0000123580070 0x08ffc00001235800 0xffe0000003fc0003 0xe8ffe0000003fc00

def z95 : W := mkw 0xa80000036b5800f0 0x08a80000036b5800 0xf8000007fffc00c1 0xf9f8000007fffc00

def z96 : W := mkw 0x000041003190ea24 0x80000041003190ea 0x000000007381c080 0x00000000007381c0

def z97 : W := mkw 0xffc60583ebd948f8 0x09ffc60583ebd948 0xffee0707fffdc0cb 0xfdffee0707fffdc0

def z98 : W := mkw 0x0000c3101080ea04 0x800000c3101080ea 0x0001c7180003ff3c 0x020001c7180003ff

def z99 : W := mkw 0x451604a582630449 0x01451604a5826304 0xc71e07e78060002e 0xe5c71e07e7806000

def z100 : W := mkw 0x000000036b5800f0 0x08000000036b5800 0x00000007fffc00c0 0x1900000007fffc00

def z101 : W := mkw 0x000041001080ea04 0x80000041001080ea 0x000000000003ff00 0x00000000000003ff

def z102 : W := mkw 0xfffdbefc04261501 0x44fffdbefc042615 0xfffffffc0c6c003f 0xe6fffffffc0c6c00

def z103 : W := mkw 0xbac9a21000000000 0x04bac9a210000000 0x3001c00000000000 0x023001c000000000

def z104 : W := mkw 0x12b0db7c35b6ff25 0xc012b0db7c35b6ff 0x3691fff87393ffff 0x7a3691fff87393ff

def z105 : W := mkw 0x450605a182e14c49 0x01450605a182e14c 0xc70e07e383e1ccaa 0x4dc70e07e383e1cc

def z106 : W := mkw 0xfff0186f6f7e15f1 0x48fff0186f6f7e15 0xfff038fffffe3ff7 0xf9fff038fffffe3f

def z107 : W := mkw 0x45160da586e75d49 0x4145160da586e75d 0xc71e07e78fffffee 0xfdc71e07e78fffff

def z108 : W := mkw 0xffedf7d81080ea04 0x84ffedf7d81080ea 0xfffffff80003ff3f 0xe6fffffff80003ff

def z109 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3601c7007381c088 0x423601c7007381c0

def z110 : W := mkw 0xffefb7d982c14848 0x05ffefb7d982c148 0xfffffffb8381c0bf 0xe7fffffffb8381c0

def z111 : W := mkw 0x57edb6d800000000 0x0457edb6d8000000 0x07fffff80000003e 0x0607fffff8000000

def z112 : W := mkw 0xa800000248000080 0x00a8000002480000 0xf8000007fc0000c1 0xf1f8000007fc0000

def z113 : W := mkw 0xffdb6807ff5bb0fe 0x0affdb6807ff5bb0 0xfffff807fffff0df 0xfffffff807fffff0

def z114 : W := mkw 0x57c0000123580070 0x0857c00001235800 0x07e0000003fc0002 0x0807e0000003fc00

def z115 : W := mkw 0x450405a102e04c41 0x01450405a102e04c 0x070007e003e00c22 0x08070007e003e00c

def z116 : W := mkw 0x4506058182c14848 0x014506058182c148 0xc60e07038381c088 0x45c60e07038381c0

def z117 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xf6000003f3800080 0x41f6000003f38000

def z118 : W := mkw 0xffedf6d83110a224 0x84ffedf6d83110a2 0xfffffff87010333f 0xf6fffffff8701033

def z119 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0x381ff8007c03f01d 0x16381ff8007c03f0

def z120 : W := mkw 0xffc0000000000000 0x00ffc00000000000 0xf600000000000000 0x40f6000000000000

def z121 : W := mkw 0x4504048000000000 0x0045040480000000 0xc11e00e000000000 0x84c11e00e0000000

def z122 : W := mkw 0xed4000034a4800d0 0x08ed4000034a4800 0xc96000078c6c0000 0x81c96000078c6c00

def z123 : W := mkw 0xffc0c3137bd8eaf4 0x88ffc0c3137bd8ea 0xffe1c71fffffffff 0xfbffe1c71fffffff

def z124 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0000007800000c0 0xe1c0000007800000

def z125 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x0681c7180393ff3e 0x0a0681c7180393ff

def z126 : W := mkw 0x0030186c04261501 0x400030186c042615 0x081038fc0c023f75 0xb0081038fc0c023f

def z127 : W := mkw 0xa83ffededc03b08e 0x06a83ffededc03b0 0xf81ffffffc03f0fd 0xf7f81ffffffc03f0

def z128 : W := mkw 0x0012012582e34c49 0x010012012582e34c 0x0000000783e3ccc0 0x090000000783e3cc

def z129 : W := mkw 0xbae9b25800000000 0x04bae9b258000000 0x38e1f81800000011 0x0238e1f818000000

def z130 : W := mkw 0xffdb6806dc03b08e 0x02ffdb6806dc03b0 0xfffff807fc03f0df 0xf7fffff807fc03f0

def z131 : W := mkw 0x0020106800240501 0x4000201068002405 0x016000e0006c0000 0x00016000e0006c00

def z132 : W := mkw 0x1280831000804800 0x0012808310008048 0x3681c7180383ccff 0x6a3681c7180383cc

def z133 : W := mkw 0x0010080404021000 0x0000100804040210 0x000000040c023040 0x10000000040c0230

def z134 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffffc0c7c007f 0xfefffffffc0c7c00

def z135 : W := mkw 0x0012002582630449 0x0100120025826304 0x0000000780600000 0x0100000007806000

def z136 : W := mkw 0x0010080404021000 0x0000100804040210 0x09f038040c7e3057 0xb809f038040c7e30

def z137 : W := mkw 0x0030186c04261501 0x400030186c042615 0x09f038f800023f37 0xa009f038f800023f

def z138 : W := mkw 0x45160da586e35c49 0x0145160da586e35c 0xcf1e3fe78fe3fcff 0xfdcf1e3fe78fe3fc

def z139 : W := mkw 0x000040001000a004 0x00000040001000a0 0x3081c0187013ffff 0x7a3081c0187013ff

def z140 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf01ff803f003f09c 0x47f01ff803f003f0

def z141 : W := mkw 0x1280000021100020 0x0012800000211000 0x36800000739000c3 0x7836800000739000

def z142 : W := mkw 0xbae9f2583110a224 0x84bae9f2583110a2 0x38e1f81870103311 0x1238e1f818701033

def z143 : W := mkw 0xa83b786edc27b58f 0x42a83b786edc27b5 0xf9fff8fffc7fffff 0xfff9fff8fffc7fff

def z144 : W := mkw 0x1280000021100020 0x0012800000211000 0x3fe000047ffc00c3 0xf83fe000047ffc00

def z145 : W := mkw 0x0020104800040100 0x4000201048000401 0x00e00018001c0300 0x0000e00018001c03

def z146 : W := mkw 0x0006058080814808 0x0100060580808148 0x000e07000001c008 0x04000e07000001c0

def z147 : W := mkw 0xffed34c800000000 0x04ffed34c8000000 0xfffe38e000000003 0xe4fffe38e0000000

def z148 : W := mkw 0xffd20127ebfb4cf9 0x09ffd20127ebfb4c 0xffe00007ffffccc3 0xf9ffe00007ffffcc

def z149 : W := mkw 0x0012012582e34c49 0x010012012582e34c 0xc01e000783e3cccc 0xedc01e000783e3cc

def z150 : W := mkw 0xfffdfffc35b6ff25 0xc4fffdfffc35b6ff 0xfffffffc7fffffff 0xfefffffffc7fffff

def z151 : W := mkw 0x0010002400220401 0x0000100024002204 0x011000e400620c66 0xa8011000e400620c

def z152 : W := mkw 0xa800000248000080 0x00a8000002480000 0xc80000078c000000 0x81c80000078c0000

def z153 : W := mkw 0x00000002691800b0 0x0800000002691800 0x000000007c1c0000 0x10000000007c1c00

def z154 : W := mkw 0xffcfa79182c14848 0x05ffcfa79182c148 0xf60fc7038381c088 0x47f60fc7038381c0

def z155 : W := mkw 0x12adf7d83190ea24 0x8412adf7d83190ea 0x369ffff87393ffff 0x7e369ffff87393ff

def z156 : W := mkw 0x128041003190ea24 0x80128041003190ea 0x368000007393ffc3 0x78368000007393ff

def z157 : W := mkw 0x45361ded86e75d49 0x4145361ded86e75d 0xcffe3fff8fffffff 0xfdcffe3fff8fffff

def z158 : W := mkw 0x5786c791b3d1ea6c 0x815786c791b3d1ea 0xf60fc703f381c088 0x47f60fc703f381c0

def z159 : W := mkw 0x451645a592e3ec4d 0x01451645a592e3ec 0xf71fc7e7f3e3fcff 0xfff71fc7e7f3e3fc

def z160 : W := mkw 0x1280821000000000 0x0012808210000000 0x3681c7180000003f 0x623681c718000000

def z161 : W := mkw 0xffc082136b5800f0 0x08ffc082136b5800 0xffe1c71ffffc00ff 0xfbffe1c71ffffc00

def z162 : W := mkw 0xed7f7ccedc03b08e 0x06ed7f7ccedc03b0 0xf97ff8e7fc03f0dd 0xf7f97ff8e7fc03f0

def z163 : W := mkw 0xffc968037f58b0f6 0x0affc968037f58b0 0xffe1f807fffc30d3 0xfbffe1f807fffc30

def z164 : W := mkw 0x003dbefc04261501 0x44003dbefc042615 0x001ffff800023f3c 0x06001ffff800023f

def z165 : W := mkw 0x000040001000a004 0x00000040001000a0 0x3001c0007003f0dd 0x723001c0007003f0

def z166 : W := mkw 0x0020104800000000 0x0000201048000000 0x001038f800000034 0x00001038f8000000

def z167 : W := mkw 0x0012092586e75d49 0x410012092586e75d 0x000000078fffffc0 0x19000000078fffff

def z168 : W := mkw 0x0000080004001000 0x0000000800040010 0x080038000c003011 0x10080038000c0030

def z169 : W := mkw 0x0000000000000000 0x0000000000000000 0x06000000038000c2 0x6806000000038000

def z170 : W := mkw 0x002496d800000000 0x04002496d8000000 0x000007f800000020 0x00000007f8000000

def z171 : W := mkw 0xffcda69000000000 0x04ffcda690000000 0xfe1fff000000001d 0xe6fe1fff00000000

def z172 : W := mkw 0x001008276f7e15f1 0x48001008276f7e15 0x00000007fffe3fc0 0x1900000007fffe3f

def z173 : W := mkw 0x0020184804041100 0x4000201848040411 0x08e038180c1e3f77 0x3808e038180c1e3f

def z174 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc11e07e78063cc2c 0x85c11e07e78063cc

def z175 : W := mkw 0xed6db6d800000000 0x04ed6db6d8000000 0xc97ffff80000003c 0x86c97ffff8000000

def z176 : W := mkw 0x4516c7b592e3ee4d 0x814516c7b592e3ee 0xc71fc7ff83e3fffe 0xefc71fc7ff83e3ff

def z177 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3081c0187393ffd1 0x1a3081c0187393ff

def z178 : W := mkw 0x0012000480030008 0x0000120004800300 0x001e00000003c00c 0x04001e00000003c0

def z179 : W := mkw 0x12e0925800000000 0x0412e09258000000 0x00e0001800000000 0x0000e00018000000

def z180 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xff600007ffec0080 0xc1ff600007ffec00

def z181 : W := mkw 0xa81b6826dc27b58f 0x42a81b6826dc27b5 0xf81ff807fc7fffdd 0xfff81ff807fc7fff

def z182 : W := mkw 0x1280821021100220 0x8012808210211002 0x0080001800100300 0x0000800018001003

def z183 : W := mkw 0x00124927dee3fccf 0x0300124927dee3fc 0x00000007ffe3fcc0 0x1900000007ffe3fc

def z184 : W := mkw 0x12a0d37831b4ef25 0xc012a0d37831b4ef 0x37e1c7f873ffffff 0x7a37e1c7f873ffff

def z185 : W := mkw 0xffc0c3137bd8eaf4 0x88ffc0c3137bd8ea 0xf681c71bf393ffff 0x7bf681c71bf393ff

def z186 : W := mkw 0xed5605a7caeb4cd9 0x09ed5605a7caeb4c 0xcf7e07e78fefccee 0xedcf7e07e78fefcc

def z187 : W := mkw 0xa80b2002c801008a 0x02a80b2002c80100 0xc00e000380000000 0x05c00e0003800000

def z188 : W := mkw 0xbae9b25800000000 0x04bae9b258000000 0x39f1f8f800000037 0xa239f1f8f8000000

def z189 : W := mkw 0x1280821000000000 0x0012808210000000 0x3681c71800123f7f 0x7a3681c71800123f

def z190 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xf9fff8f800000011 0x86f9fff8f8000000

def z191 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xcffe3ff800000022 0x84cffe3ff8000000

def z192 : W := mkw 0x1280c2103110a224 0x801280c2103110a2 0x3681c7187010333f 0x723681c718701033

def z193 : W := mkw 0x57b6dffdb7f7ff6d 0xc157b6dffdb7f7ff 0xffffffffffffffff 0xffffffffffffffff

def z194 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xffe00003f3800083 0xe1ffe00003f38000

def z195 : W := mkw 0xba89a21000000000 0x00ba89a210000000 0xfe9fff180000003f 0xe6fe9fff18000000

def z196 : W := mkw 0x0030106c00220401 0x000030106c002204 0x09f038fc00620c77 0xa809f038fc00620c

def z197 : W := mkw 0xa81b200480030008 0x00a81b2004800300 0xf81ff8078003c0dd 0xe7f81ff8078003c0

def z198 : W := mkw 0x0000010000804800 0x0000000100008048 0x060007000381c088 0x40060007000381c0

def z199 : W := mkw 0xed4000034a4800d0 0x08ed4000034a4800 0xc9e000078c7c0043 0xb9c9e000078c7c00

def z200 : W := mkw 0x0010000400020000 0x0000100004000200 0x0010000400020044 0xa000100004000200

def z201 : W := mkw 0xffcda6936b5800f0 0x0cffcda6936b5800 0xffefc707fffc00cb 0xffffefc707fffc00

def z202 : W := mkw 0x451f6da596e3fc4f 0x03451f6da596e3fc 0xc71fffe783e3fcfe 0xefc71fffe783e3fc

def z203 : W := mkw 0x57c0c31133d8ea74 0x8857c0c31133d8ea 0x37e1c71873ffffff 0x7a37e1c71873ffff

def z204 : W := mkw 0x57c0000000000000 0x0057c00000000000 0x07e0000000000002 0x0007e00000000000

def z205 : W := mkw 0xffe0106b6b7c05f1 0x48ffe0106b6b7c05 0xffe000fffffc0fe3 0xf9ffe000fffffc0f

def z206 : W := mkw 0x0012000480030008 0x0000120004800300 0xc01e000780000000 0x85c01e0007800000

def z207 : W := mkw 0xfffdbeff6f7e15f1 0x4cfffdbeff6f7e15 0xfffffffffffe3fff 0xfffffffffffffe3f

def z208 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xf7efc7f80000002a 0x46f7efc7f8000000

def z209 : W := mkw 0xbae0184a6d1c11b0 0x48bae0184a6d1c11 0x38e038187c1c3311 0x1038e038187c1c33

def z210 : W := mkw 0xa81beb16dc83fa8e 0x82a81beb16dc83fa 0xf81fff1ffc03fffd 0xf7f81fff1ffc03ff

def z211 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e1c088 0xc5c71e07e783e1c0

def z212 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080001800123f77 0x380080001800123f

def z213 : W := mkw 0xa81b2806cc03108a 0x02a81b2806cc0310 0xc81e38078c023055 0xb5c81e38078c0230

def z214 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xfee00003ff9c0081 0x51fee00003ff9c00

def z215 : W := mkw 0xffffb7ffebfb4cf9 0x0dffffb7ffebfb4c 0xffffffffffffccff 0xffffffffffffffcc

def z216 : W := mkw 0x003fb7fc80a34c09 0x05003fb7fc80a34c 0x001ffff80003cc3c 0x06001ffff80003cc

def z217 : W := mkw 0xbae9b25a691800b0 0x0cbae9b25a691800 0x38e1f8187c1c0011 0x1238e1f8187c1c00

def z218 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080001800000037 0x2000800018000000

def z219 : W := mkw 0xfffdbefc04261501 0x44fffdbefc042615 0xfffffff800023f3f 0xe6fffffff800023f

def z220 : W := mkw 0x000968001400b006 0x02000968001400b0 0x0001f80000003010 0x020001f800000030

def z221 : W := mkw 0x0030186f6f7e15f1 0x480030186f6f7e15 0x09f038fffffe3ff7 0xb909f038fffffe3f

def z222 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc61e07e38383ccac 0x45c61e07e38383cc

def z223 : W := mkw 0xffc405a36bf84cf1 0x09ffc405a36bf84c 0xffe007e7fffc0ce3 0xf9ffe007e7fffc0c

def z224 : W := mkw 0xa81b6826dc23b48f 0x02a81b6826dc23b4 0xf91ff8e7fc63fcff 0xfff91ff8e7fc63fc

def z225 : W := mkw 0x0000000000000000 0x0000000000000000 0x0810380000000015 0xa008103800000000

def z226 : W := mkw 0xa80b6002d801a08e 0x02a80b6002d801a0 0xf80fc007fc01c0c9 0xf7f80fc007fc01c0

def z227 : W := mkw 0xffdfee96dc03b08e 0x06ffdfee96dc03b0 0xfe1fff07fc03f0dd 0xf7fe1fff07fc03f0

def z228 : W := mkw 0xed70186f4e6e15d1 0x48ed70186f4e6e15 0xc97038e78c6c0000 0x81c97038e78c6c00

def z229 : W := mkw 0xed1605a7cae34cc9 0x01ed1605a7cae34c 0xff1e07e7ffe3ccef 0xfdff1e07e7ffe3cc

def z230 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf81ff807fc01c088 0xc7f81ff807fc01c0

def z231 : W := mkw 0x0000000000000000 0x0000000000000000 0x096000040c6c0000 0x80096000040c6c00

def z232 : W := mkw 0x0000010000804800 0x0000000100008048 0x0600070003800c22 0x080600070003800c

def z233 : W := mkw 0xa80968025c00b086 0x02a80968025c00b0 0x3801f8007c003011 0x123801f8007c0030

def z234 : W := mkw 0x000041003190ea24 0x80000041003190ea 0x060007007393ffee 0x78060007007393ff

def z235 : W := mkw 0xa800000248000080 0x00a8000002480000 0xf0000003f0000080 0x41f0000003f00000

def z236 : W := mkw 0x1290cb143592fa24 0x801290cb143592fa 0x3e91ff1c7f93ffff 0xfa3e91ff1c7f93ff

def z237 : W := mkw 0xffd008076f5a10f0 0x08ffd008076f5a10 0xfff03807fffe30d7 0xf9fff03807fffe30

def z238 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080001800103311 0x1000800018001033

def z239 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3601c7187383ffbc 0x423601c7187383ff

def z240 : W := mkw 0xa83b386ecc27158b 0x42a83b386ecc2715 0xc9fe38ff8c7e3f77 0xbdc9fe38ff8c7e3f

def z241 : W := mkw 0xffedb6da48000080 0x04ffedb6da480000 0xfffffffffc0000ff 0xf7fffffffffc0000

def z242 : W := mkw 0xbae9ba5804041100 0x44bae9ba58040411 0x38e1f8180c1c3311 0x1238e1f8180c1c33

def z243 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffff800123f7f 0xfefffffff800123f

def z244 : W := mkw 0xffc001036bd848f0 0x08ffc001036bd848 0xffe00707ffffccef 0xf9ffe00707ffffcc

def z245 : W := mkw 0xed7d3cec04261501 0x44ed7d3cec042615 0xc9fe38fc0c7e3f77 0xbcc9fe38fc0c7e3f

def z246 : W := mkw 0xffc0000248000080 0x00ffc00002480000 0xffe00007fc0000c3 0xf1ffe00007fc0000

def z247 : W := mkw 0x003dbefc04261501 0x44003dbefc042615 0x09fffffc0c7e3f7f 0xbe09fffffc0c7e3f

def z248 : W := mkw 0x001605a480a34c09 0x01001605a480a34c 0x011e07e40063cc6e 0xac011e07e40063cc

def z249 : W := mkw 0x0030186c04261501 0x400030186c042615 0x09f038fc0c6c0037 0xa009f038fc0c6c00

def z250 : W := mkw 0x0030106c00260501 0x400030106c002605 0x01f000fc007e0f66 0xa801f000fc007e0f

def z251 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc79e07ff83f3ffff 0xfdc79e07ff83f3ff

def z252 : W := mkw 0x001605a582e34c49 0x01001605a582e34c 0x001e07e783e3ccec 0x0d001e07e783e3cc

def z253 : W := mkw 0x4504048102400040 0x0045040481024000 0xc71e07e783e000ee 0xedc71e07e783e000

def z254 : W := mkw 0xfffdb6fc00220401 0x04fffdb6fc002204 0xfffffffc00620c7f 0xeefffffffc00620c

def z255 : W := mkw 0x0000002000240501 0x4000000020002405 0x00000000007c0f00 0x0800000000007c0f

def z256 : W := mkw 0x4506058182c14848 0x014506058182c148 0xc71e07e38381c0ae 0xe5c71e07e38381c0

def z257 : W := mkw 0x1280000000000000 0x0012800000000000 0x3680000000000003 0x6036800000000000

def z258 : W := mkw 0xffedb6d821100020 0x04ffedb6d8211000 0xfffffff8739000ff 0xfefffffff8739000

def z259 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf9fff807fc7ff0df 0xfff9fff807fc7ff0

def z260 : W := mkw 0xed1f2da7cee35ccb 0x03ed1f2da7cee35c 0xcf1e3fe78fe3ccee 0xedcf1e3fe78fe3cc

def z261 : W := mkw 0x0000000000000000 0x0000000000000000 0x011000e000000026 0xa0011000e0000000

def z262 : W := mkw 0x00124806dc03b08e 0x0200124806dc03b0 0x08103807fc03f0d5 0xb108103807fc03f0

def z263 : W := mkw 0xed4000034a4800d0 0x08ed4000034a4800 0xcf6000078fec00c2 0xe9cf6000078fec00

def z264 : W := mkw 0x1292c314b193ea2c 0x801292c314b193ea 0xf69fc71ff393ffff 0xfff69fc71ff393ff

def z265 : W := mkw 0x450405a102e04c41 0x01450405a102e04c 0xc70007e783e00ce2 0xe9c70007e783e00c

def z266 : W := mkw 0x000040001000a004 0x00000040001000a0 0x3001c0007001c088 0x423001c0007001c0

def z267 : W := mkw 0xa829304800000000 0x00a8293048000000 0xf9fff8f80000003f 0xe6f9fff8f8000000

def z268 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0x3fe000007ffc0003 0x183fe000007ffc00

def z269 : W := mkw 0xfffffedfff5bb0fe 0x0efffffedfff5bb0 0xfffffffffffff0ff 0xfffffffffffffff0

def z270 : W := mkw 0x1280821000000000 0x0012808210000000 0x3081c01800000011 0x023081c018000000

def z271 : W := mkw 0xffcda69000000000 0x04ffcda690000000 0xf68fc7180000003f 0x66f68fc718000000

def z272 : W := mkw 0x57c0000123580070 0x0857c00001235800 0x0600000003800000 0x0006000000038000

def z273 : W := mkw 0x4506058182c14848 0x014506058182c148 0xc70e070783e1c0ca 0xedc70e070783e1c0

def z274 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e00c22 0x8dc71e07e783e00c

def z275 : W := mkw 0xa809200000000000 0x00a8092000000000 0xc81e380000000000 0x84c81e3800000000

def z276 : W := mkw 0xffdf6da7fffbfcff 0x0bffdf6da7fffbfc 0xffffffe7fffffcff 0xffffffffe7fffffc

def z277 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3081c7187013ff3d 0x123081c7187013ff

def z278 : W := mkw 0x0020106800240501 0x4000201068002405 0x000000f800000f20 0x00000000f800000f

def z279 : W := mkw 0x57f697fd82e34c49 0x0557f697fd82e34c 0xc7fe07ff83e3ccee 0xedc7fe07ff83e3cc

def z280 : W := mkw 0x0010082404261501 0x4000100824042615 0x0000000000023f00 0x000000000000023f

def z281 : W := mkw 0x1280821021100020 0x0012808210211000 0x3681c718739000ff 0x7a3681c718739000

def z282 : W := mkw 0x57e496d800000000 0x0457e496d8000000 0xc7fe07f80000002e 0xe4c7fe07f8000000

def z283 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xcffe07e78fffccef 0xfdcffe07e78fffcc

def z284 : W := mkw 0x57e01069237c0571 0x4857e01069237c05 0x07e000f803fc0f22 0x0807e000f803fc0f

def z285 : W := mkw 0xbae9b25800000000 0x04bae9b258000000 0xf8fff8180000001d 0xe6f8fff818000000

def z286 : W := mkw 0x0020104800000000 0x0000201048000000 0x09f038fc0c7c0077 0xb809f038fc0c7c00

def z287 : W := mkw 0x4504048000000000 0x0045040480000000 0xc60e070000000008 0x44c60e0700000000

def z288 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xf61ffff80000003c 0x46f61ffff8000000

def z289 : W := mkw 0xffffbedecc03108a 0x06ffffbedecc0310 0xffffffff8c00003f 0xe7ffffffff8c0000

def z290 : W := mkw 0xed0d248000000000 0x00ed0d2480000000 0xff1fffe00000003f 0xe6ff1fffe0000000

def z291 : W := mkw 0x0030186c04261501 0x400030186c042615 0x01f038f8007e3f36 0x0801f038f8007e3f

def z292 : W := mkw 0x0010012400a24c01 0x000010012400a24c 0x071007e403e3ccee 0xe8071007e403e3cc

def z293 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xc81e3807fc03f0c0 0x95c81e3807fc03f0

def z294 : W := mkw 0xffedb6d902400040 0x04ffedb6d9024000 0xffffffff83e000ff 0xefffffffff83e000

def z295 : W := mkw 0xffcda6936b5800f0 0x0cffcda6936b5800 0xf60fc703f3800088 0x47f60fc703f38000

def z296 : W := mkw 0x00124826dc27b58f 0x4200124826dc27b5 0x00000007fc7fffc0 0x1900000007fc7fff

def z297 : W := mkw 0x0000c3101080ea04 0x800000c3101080ea 0x0081c7180013ff7f 0x3a0081c7180013ff

def z298 : W := mkw 0x0004048000000000 0x0000040480000000 0x001e07e00000002c 0x04001e07e0000000

def z299 : W := mkw 0x0032586edc27b58f 0x420032586edc27b5 0x09f038fffc7ffff7 0xb909f038fffc7fff

def z300 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3fe1c71c7fffffff 0xfa3fe1c71c7fffff

def z301 : W := mkw 0x001240049003a00c 0x00001240049003a0 0xf01fc007f003f0dd 0xf7f01fc007f003f0

def z302 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf81ff807fc003011 0x97f81ff807fc0030

def z303 : W := mkw 0xed0000034a4000c0 0x00ed0000034a4000 0xff000007ffe000c3 0xf9ff000007ffe000

def z304 : W := mkw 0x57f0186d277e1571 0x4857f0186d277e15 0x0ff038fc0ffe3f77 0xb80ff038fc0ffe3f

def z305 : W := mkw 0x0020184804041100 0x4000201848040411 0x0000381800003310 0x0000003818000033

def z306 : W := mkw 0xa809200000000000 0x00a8092000000000 0xf00fc00000000008 0x46f00fc000000000

def z307 : W := mkw 0xffc404836b5800f0 0x08ffc404836b5800 0xfffe07e7fffc00ef 0xfdfffe07e7fffc00

def z308 : W := mkw 0xa82db6d800000000 0x04a82db6d8000000 0xf81ffff80000003d 0xe6f81ffff8000000

def z309 : W := mkw 0xfff0186c04261501 0x40fff0186c042615 0xfff038fc0c7e3f77 0xf8fff038fc0c7e3f

def z310 : W := mkw 0xba800002691000a0 0x00ba800002691000 0xfe800007ff9000c3 0xf9fe800007ff9000

def z311 : W := mkw 0xffdbeb17ffdbfafe 0x8affdbeb17ffdbfa 0xffffff1fffffffff 0xffffffff1fffffff

def z312 : W := mkw 0x5784c7903190ea24 0x805784c7903190ea 0xf79fc7f87393ffff 0xfef79fc7f87393ff

def z313 : W := mkw 0x450404a102600441 0x01450404a1026004 0x010000e000600000 0x00010000e0006000

def z314 : W := mkw 0x578487b123f04e61 0x81578487b123f04e 0x078007f803f00f22 0x08078007f803f00f

def z315 : W := mkw 0xffcfe692d801a08e 0x06ffcfe692d801a0 0xf60fc703f001c088 0x47f60fc703f001c0

def z316 : W := mkw 0xffedbed804041100 0x44ffedbed8040411 0xfffffff80c1c333f 0xf6fffffff80c1c33

def z317 : W := mkw 0xffffffdefd93faae 0x86ffffffdefd93fa 0xffffffffff93ffff 0xffffffffffff93ff

def z318 : W := mkw 0x0002000080010008 0x0000020000800100 0xc00e00038001c088 0x45c00e00038001c0

def z319 : W := mkw 0xbac00002691800b0 0x08bac00002691800 0x39e000047c7c0043 0xb839e000047c7c00

def z320 : W := mkw 0xa830186e4c261581 0x40a830186e4c2615 0xf9f038fffc7e3ff7 0xf9f9f038fffc7e3f

def z321 : W := mkw 0x00124807ff5bb0fe 0x0a00124807ff5bb0 0x00000007fffff0c0 0x1900000007fffff0

def z322 : W := mkw 0x0010002400220401 0x0000100024002204 0x019000fc00723f77 0xb8019000fc00723f

def z323 : W := mkw 0x002df7d81080ea04 0x84002df7d81080ea 0x001ffff80003ff3c 0x06001ffff80003ff

def z324 : W := mkw 0x451604a582630449 0x01451604a5826304 0xc11e00e78063c0cc 0xe5c11e00e78063c0

def z325 : W := mkw 0x0000000000000000 0x0000000000000000 0x080000040c000041 0xb0080000040c0000

def z326 : W := mkw 0x002db6d800000000 0x04002db6d8000000 0x09fffff80000003f 0xa609fffff8000000

def z327 : W := mkw 0x4500000102400040 0x0045000001024000 0x0700000003e00002 0x080700000003e000

def z328 : W := mkw 0xa839786e5c26b587 0x42a839786e5c26b5 0x39f1f8fc7c7e3f77 0xba39f1f8fc7c7e3f

def z329 : W := mkw 0x4504058102c04840 0x014504058102c048 0x0600070003800000 0x0006000700038000

def z330 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xfffffffbf38000bf 0xe7fffffffbf38000

def z331 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3681c7187381c0bf 0x623681c7187381c0

def z332 : W := mkw 0x0030db7c14a6ff05 0xc00030db7c14a6ff 0x0011fff80003ff3c 0x020011fff80003ff

def z333 : W := mkw 0x0000012102e04c41 0x010000012102e04c 0x0000000003e00c00 0x080000000003e00c

def z334 : W := mkw 0x0029b25800000000 0x040029b258000000 0x0001f81800000010 0x020001f818000000

def z335 : W := mkw 0xffe0104b6b5800f0 0x08ffe0104b6b5800 0xfff038fffffc00f7 0xf9fff038fffffc00

def z336 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000020c66 0x280000000000020c

def z337 : W := mkw 0x0000000000000000 0x0000000000000000 0x30000000700000c1 0x7030000000700000

def z338 : W := mkw 0x456414c800000000 0x04456414c8000000 0x016000e000000000 0x00016000e0000000

def z339 : W := mkw 0x001605a480a34c09 0x01001605a480a34c 0xc01e07e78003ccec 0xe5c01e07e78003cc

def z340 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3601c7007383ccee 0x6a3601c7007383cc

def z341 : W := mkw 0xffed34cb6b5800f0 0x0cffed34cb6b5800 0xfffe38e7fffc00c3 0xfdfffe38e7fffc00

def z342 : W := mkw 0x4512000582430048 0x0045120005824300 0xc71e000783e3c0ce 0xedc71e000783e3c0

def z343 : W := mkw 0xba89e3103190ea24 0x80ba89e3103190ea 0xfe9fff187393ffff 0xfefe9fff187393ff

def z344 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfeefff1800000019 0x46feefff18000000

def z345 : W := mkw 0x0030186c04261501 0x400030186c042615 0x08e0381c0c7e3f51 0x1808e0381c0c7e3f

def z346 : W := mkw 0xfffb786fff7fb5ff 0x4afffb786fff7fb5 0xfffff8ffffffffff 0xfffffff8ffffffff

def z347 : W := mkw 0x4516058582c34848 0x014516058582c348 0xc61e07078383c0cc 0xe5c61e07078383c0

def z348 : W := mkw 0x451605a7ebfb4cf9 0x09451605a7ebfb4c 0xc71e07e7ffffccee 0xfdc71e07e7ffffcc

def z349 : W := mkw 0x1280c2103110a224 0x801280c2103110a2 0x3081c01870123f77 0x3a3081c01870123f

def z350 : W := mkw 0x000b60009001a00e 0x02000b60009001a0 0x000fc0000001c008 0x06000fc0000001c0

def z351 : W := mkw 0x4504048000000000 0x0045040480000000 0x070007e000000022 0x00070007e0000000

def z352 : W := mkw 0x0030184c04021000 0x000030184c040210 0x09f038fc0c023077 0xb009f038fc0c0230

def z353 : W := mkw 0xa80b6802dc01b08e 0x02a80b6802dc01b0 0xf80ff803fc01f099 0x57f80ff803fc01f0

def z354 : W := mkw 0xffc0000000000000 0x00ffc00000000000 0xffe000040c7c0043 0xf8ffe000040c7c00

def z355 : W := mkw 0x57c0831123d84a70 0x8857c0831123d84a 0x07e0071803fc0f22 0x0807e0071803fc0f

def z356 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000123f40 0x180000000000123f

def z357 : W := mkw 0xffedf7d83190ea24 0x84ffedf7d83190ea 0xfffffff87381c0bf 0xe6fffffff87381c0

def z358 : W := mkw 0x0020184804041100 0x4000201848040411 0x08e038180c1c3311 0x1008e038180c1c33

def z359 : W := mkw 0xffcb6003fb59a0fe 0x0affcb6003fb59a0 0xffefc007fffdc0cb 0xffffefc007fffdc0

def z360 : W := mkw 0xba8be312f991eaae 0x82ba8be312f991ea 0xf60fc703f381c088 0x47f60fc703f381c0

def z361 : W := mkw 0x57c000036b5800f0 0x0857c000036b5800 0x07e00007fffc00c2 0x1907e00007fffc00

def z362 : W := mkw 0xed1f65a7dae3eccf 0x03ed1f65a7dae3ec 0xf71fc7e7f3e3ccee 0xeff71fc7e7f3e3cc

def z363 : W := mkw 0x0000010000804800 0x0000000100008048 0x000007000003cc2c 0x00000007000003cc

def z364 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3681c71873903f33 0x1a3681c71873903f

def z365 : W := mkw 0xba9beb16fd93faae 0x82ba9beb16fd93fa 0xfe1fff07ff83f0dd 0xf7fe1fff07ff83f0

def z366 : W := mkw 0x0030186c04261501 0x400030186c042615 0x097038e40c6e0c66 0xa8097038e40c6e0c

def z367 : W := mkw 0x453615ed82e34c49 0x01453615ed82e34c 0xcffe3fff83e3ccff 0xedcffe3fff83e3cc

def z368 : W := mkw 0xa80968025c00b086 0x02a80968025c00b0 0xf81ff8007c00301d 0xf6f81ff8007c0030

def z369 : W := mkw 0x452414c800000000 0x00452414c8000000 0xcffe3ff80000003f 0xe4cffe3ff8000000

def z370 : W := mkw 0x000040003110a224 0x80000040003110a2 0x0000000070103300 0x1000000000701033

def z371 : W := mkw 0xba80c3127990eaa4 0x80ba80c3127990ea 0xfe81c71fff93ffff 0xfbfe81c71fff93ff

def z372 : W := mkw 0x4516048480030008 0x0045160484800300 0xc71e07e78003c0ee 0xe5c71e07e78003c0

def z373 : W := mkw 0x0030186c04261501 0x400030186c042615 0x009038f800123f77 0x38009038f800123f

def z374 : W := mkw 0x001605a480a34c09 0x01001605a480a34c 0x061e07e00383ccee 0x6c061e07e00383cc

def z375 : W := mkw 0x0030186c04261501 0x400030186c042615 0x08f038f80c1e3f35 0x1008f038f80c1e3f

def z376 : W := mkw 0xa83b784edc07b18e 0x42a83b784edc07b1 0xf8fff81ffc1ff3dd 0xf7f8fff81ffc1ff3

def z377 : W := mkw 0x4500010102c04840 0x004500010102c048 0xc700070783e3ccee 0xe9c700070783e3cc

def z378 : W := mkw 0xed1f25a582e34c49 0x01ed1f25a582e34c 0xff1fffe783e3ccff 0xefff1fffe783e3cc

def z379 : W := mkw 0x0030596c35b6ff25 0xc00030596c35b6ff 0x09f038fc7ffffff7 0xb809f038fc7fffff

def z380 : W := mkw 0x0030186c04261501 0x400030186c042615 0x01e000fc0c7e3f62 0x1801e000fc0c7e3f

def z381 : W := mkw 0x453fb7fd82e34c49 0x05453fb7fd82e34c 0xc71fffff83e3ccfe 0xefc71fffff83e3cc

def z382 : W := mkw 0xed6d34c800000000 0x04ed6d34c8000000 0xc9fe38f800000037 0xa4c9fe38f8000000

def z383 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xf7e00003f3fc0082 0x49f7e00003f3fc00

def z384 : W := mkw 0x0030186c04261501 0x400030186c042615 0x097038e40c7e3f40 0x98097038e40c7e3f

def z385 : W := mkw 0x0000c3101080ea04 0x800000c3101080ea 0x0001c7000001c008 0x020001c7000001c0

def z386 : W := mkw 0x001beb149483fa0e 0x82001beb149483fa 0x001fff180003ff3c 0x06001fff180003ff

def z387 : W := mkw 0xffedb6da691800b0 0x0cffedb6da691800 0xfffffff87c1c003f 0xf6fffffff87c1c00

def z388 : W := mkw 0x0000000000000000 0x0000000000000000 0xc01e00000000000c 0xe4c01e0000000000

def z389 : W := mkw 0xa81b6927dee3fccf 0x03a81b6927dee3fc 0xf81ff807ffe3fcdd 0xfff81ff807ffe3fc

def z390 : W := mkw 0xbac00002691800b0 0x08bac00002691800 0x3ee000007f9c00c3 0x783ee000007f9c00

def z391 : W := mkw 0xffd604a7eb7b04f9 0x09ffd604a7eb7b04 0xfffe00e7fffc00c3 0xfdfffe00e7fffc00

def z392 : W := mkw 0xa800000248000080 0x00a8000002480000 0x380000007c000001 0x10380000007c0000

def z393 : W := mkw 0x002d34c800000000 0x04002d34c8000000 0x001e38e000000000 0x04001e38e0000000

def z394 : W := mkw 0x1290c33431b2ee25 0x801290c33431b2ee 0x3791c7fc73f3ffff 0xfa3791c7fc73f3ff

def z395 : W := mkw 0x0030db7c14a6ff05 0xc00030db7c14a6ff 0x09f1fffc0c7fff7f 0xba09f1fffc0c7fff

def z396 : W := mkw 0x0012012480a34c09 0x010012012480a34c 0x000000000003cc00 0x00000000000003cc

def z397 : W := mkw 0x0000c3103190ea24 0x800000c3103190ea 0x0001c7187393fffc 0x1a0001c7187393ff

def z398 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z399 : W := mkw 0x0000821000000000 0x0000008210000000 0x0001c7180000003c 0x020001c718000000

def z400 : W := mkw 0x0020186804241501 0x4000201868042415 0x09e038f80c7c3f33 0x1809e038f80c7c3f

def z401 : W := mkw 0xa8124806dc03b08e 0x02a8124806dc03b0 0xf8000007fc03f0c1 0xf1f8000007fc03f0

def z402 : W := mkw 0x0000080004041100 0x4000000800040411 0x000000000c1c3300 0x10000000000c1c33

def z403 : W := mkw 0xfffdbedc04021000 0x04fffdbedc040210 0xfffffffc0c02307f 0xf6fffffffc0c0230

def z404 : W := mkw 0xffdfa7b582e34c49 0x05ffdfa7b582e34c 0xf71fc7e783e3ccee 0xeff71fc7e783e3cc

def z405 : W := mkw 0x451604a582630449 0x01451604a5826304 0xc71e00e783e000c2 0xedc71e00e783e000

def z406 : W := mkw 0x001f6da494a3fc0f 0x03001f6da494a3fc 0x001fffe00003fc3c 0x06001fffe00003fc

def z407 : W := mkw 0x0000c3101080ea04 0x800000c3101080ea 0x0601c7180383fffe 0x6a0601c7180383ff

def z408 : W := mkw 0x1292c335b3f3ee6d 0x811292c335b3f3ee 0x3681c71ff3f3ffff 0x7b3681c71ff3f3ff

def z409 : W := mkw 0xa809200248000080 0x00a8092002480000 0xf81ff807fc0000dd 0xf7f81ff807fc0000

def z410 : W := mkw 0xa840000248080090 0x08a8400002480800 0x086000000c0c0000 0x00086000000c0c00

def z411 : W := mkw 0xed70186f4e6e15d1 0x48ed70186f4e6e15 0xc9f038ff8c7e3f77 0xb9c9f038ff8c7e3f

def z412 : W := mkw 0x0032186c84271509 0x400032186c842715 0xc9fe38ff8c7fffff 0xfdc9fe38ff8c7fff

def z413 : W := mkw 0x5796c7b5b3f3ee6d 0x815796c7b5b3f3ee 0xf71fc7e7f3e3ccee 0xeff71fc7e7f3e3cc

def z414 : W := mkw 0x0000000000000000 0x0000000000000000 0x060007000000002e 0x6006000700000000

def z415 : W := mkw 0xffc0c3137bd8eaf4 0x88ffc0c3137bd8ea 0xf601c703f381c088 0x43f601c703f381c0

def z416 : W := mkw 0xffedb6db4a4800d0 0x0cffedb6db4a4800 0xffffffff8c6c003f 0xe7ffffffff8c6c00

def z417 : W := mkw 0xffd20007eb5b00f8 0x08ffd20007eb5b00 0xfffe0007ffffc0cf 0xfdfffe0007ffffc0

def z418 : W := mkw 0x1280c2101000a004 0x001280c2101000a0 0x3681c7187003f0ff 0x723681c7187003f0

def z419 : W := mkw 0x0010002400220401 0x0000100024002204 0x011000e400600000 0x80011000e4006000

def z420 : W := mkw 0xed4000036b5800f0 0x08ed4000036b5800 0xc9600007fffc00c0 0x99c9600007fffc00

def z421 : W := mkw 0xffffffffdee3fccf 0x07ffffffffdee3fc 0xffffffffffe3fcff 0xffffffffffffe3fc

def z422 : W := mkw 0x128000036b5800f0 0x08128000036b5800 0x36800007fffc00c3 0x7936800007fffc00

def z423 : W := mkw 0x00124806dc03b08e 0x0200124806dc03b0 0xc01e0007fc03f0cc 0xf5c01e0007fc03f0

def z424 : W := mkw 0xa80928024c001082 0x02a80928024c0010 0x080038000c000000 0x00080038000c0000

def z425 : W := mkw 0xa81008064c021080 0x00a81008064c0210 0xf8103807fc0230d5 0xf1f8103807fc0230

def z426 : W := mkw 0x000040001000a004 0x00000040001000a0 0x0001c0000003f01c 0x020001c0000003f0

def z427 : W := mkw 0x12a0937821b44f21 0xc012a0937821b44f 0x07e007f803fc0f22 0x0807e007f803fc0f

def z428 : W := mkw 0xffedb6d923580070 0x0cffedb6d9235800 0xfffffff803fc003f 0xeefffffff803fc00

def z429 : W := mkw 0xffe496d800000000 0x04ffe496d8000000 0xffe007f800000023 0xe0ffe007f8000000

def z430 : W := mkw 0x003ffedc9403b00e 0x06003ffedc9403b0 0x001ffff80003f03c 0x06001ffff80003f0

def z431 : W := mkw 0xed4000034a4800d0 0x08ed4000034a4800 0xf9600007fc6c00c1 0xf1f9600007fc6c00

def z432 : W := mkw 0x0010082404221401 0x0000100824042214 0x091038e40c623c77 0xb8091038e40c623c

def z433 : W := mkw 0xbac00002691800b0 0x08bac00002691800 0xf8e00007fc1c00c1 0xf1f8e00007fc1c00

def z434 : W := mkw 0x00120127ebfb4cf9 0x0900120127ebfb4c 0x00000007ffffccc0 0x1900000007ffffcc

def z435 : W := mkw 0x451605a480a34c09 0x01451605a480a34c 0xc71e07e00003cc2e 0xe4c71e07e00003cc

def z436 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000040c7c0040 0x18000000040c7c00

def z437 : W := mkw 0x0020106800240501 0x4000201068002405 0x09f038f8007c0f37 0xa809f038f8007c0f

def z438 : W := mkw 0x0010080404021000 0x0000100804040210 0x0890381c0c123f77 0xb80890381c0c123f

def z439 : W := mkw 0xffedf7db7bd8eaf4 0x8cffedf7db7bd8ea 0xffffffffffffffff 0xffffffffffffffff

def z440 : W := mkw 0x57e496d923580070 0x0c57e496d9235800 0x07e007f803fc0022 0x0807e007f803fc00

def z441 : W := mkw 0x0002010182c14848 0x010002010182c148 0x000000038381c080 0x01000000038381c0

def z442 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc11e00e783e3ccc0 0x8dc11e00e783e3cc

def z443 : W := mkw 0xfffffedc9403b00e 0x06fffffedc9403b0 0xfffffff80003f03f 0xe6fffffff80003f0

def z444 : W := mkw 0x1280c2103110a224 0x801280c2103110a2 0x3001c00070000000 0x023001c000700000

def z445 : W := mkw 0x0000000000000000 0x0000000000000000 0x01e00000007c0002 0x0801e00000007c00

def z446 : W := mkw 0x000000036b5800f0 0x08000000036b5800 0x00000003f3800080 0x0100000003f38000

def z447 : W := mkw 0xffedb7d800804800 0x04ffedb7d8008048 0xfffffff80383ccff 0xeefffffff80383cc

def z448 : W := mkw 0x0000010021904a20 0x800000010021904a 0x0000000003900f00 0x080000000003900f

def z449 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xfe000007ff8000c1 0xf1fe000007ff8000

def z450 : W := mkw 0xed1b6807de43b0ce 0x02ed1b6807de43b0 0xff1ff807ffe3f0df 0xffff1ff807ffe3f0

def z451 : W := mkw 0x4512012582e34c49 0x014512012582e34c 0xc700000783e3ccc2 0xe9c700000783e3cc

def z452 : W := mkw 0xed3f7defdee7fdcf 0x43ed3f7defdee7fd 0xffffffffffffffff 0xffffffffffffffff

def z453 : W := mkw 0xed5604a7ca6b04d9 0x09ed5604a7ca6b04 0xc97e00e78c6c0000 0x85c97e00e78c6c00

def z454 : W := mkw 0xa81b68049403b00e 0x02a81b68049403b0 0xf81ff8000003f01d 0xe6f81ff8000003f0

def z455 : W := mkw 0x4500000102400040 0x0045000001024000 0xc100000780600000 0x81c1000007806000

def z456 : W := mkw 0xba9b6806fd13b0ae 0x02ba9b6806fd13b0 0xfe9ff807ff93f0df 0xfffe9ff807ff93f0

def z457 : W := mkw 0xbac0c3127998eab4 0x88bac0c3127998ea 0x3ee1c7187f9fffff 0x7a3ee1c7187f9fff

def z458 : W := mkw 0x12a0925800000000 0x0012a09258000000 0x3ff1fff80000003f 0xe23ff1fff8000000

def z459 : W := mkw 0x57c405a123f84c71 0x0957c405a123f84c 0x07e007e003fc0c22 0x0807e007e003fc0c

def z460 : W := mkw 0x1280831021904a20 0x801280831021904a 0x3680071873900fe3 0x783680071873900f

def z461 : W := mkw 0xed7f35ed82e34c49 0x05ed7f35ed82e34c 0xcf7e3fe783e3ccee 0xedcf7e3fe783e3cc

def z462 : W := mkw 0x0030186c04261501 0x400030186c042615 0x001038e000000000 0x00001038e0000000

def z463 : W := mkw 0xed1f6ca7de63b4cf 0x03ed1f6ca7de63b4 0xf91ff8e7fc63f0dd 0xf7f91ff8e7fc63f0

def z464 : W := mkw 0xffedb7d821904a20 0x84ffedb7d821904a 0xfffffff803900f3f 0xeefffffff803900f

def z465 : W := mkw 0xffd605a582e34c49 0x01ffd605a582e34c 0xfffe07e783e3ccef 0xedfffe07e783e3cc

def z466 : W := mkw 0xffffb6dc80030008 0x04ffffb6dc800300 0xffffffff8003c0ff 0xe7ffffffff8003c0

def z467 : W := mkw 0xa81b6807ff5bb0fe 0x0aa81b6807ff5bb0 0xf81ff807fffff0dd 0xfff81ff807fffff0

def z468 : W := mkw 0xfffffefedc27b58f 0x46fffffefedc27b5 0xfffffffffc7fffff 0xfffffffffffc7fff

def z469 : W := mkw 0x57e496d800000000 0x0457e496d8000000 0x0ff03ff800000037 0xa00ff03ff8000000

def z470 : W := mkw 0x0000831000804a00 0x800000831000804a 0x0000071800000f20 0x000000071800000f

def z471 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf00fc007fc03f0c8 0x57f00fc007fc03f0

def z472 : W := mkw 0xba9bea16fd13b2ae 0x82ba9bea16fd13b2 0xf89ff81ffc13f3dd 0xf7f89ff81ffc13f3

def z473 : W := mkw 0x00124906fd93faae 0x8200124906fd93fa 0x00000007ff93ffc0 0x1900000007ff93ff

def z474 : W := mkw 0xffc0000102400040 0x00ffc00001024000 0xffe0000783e000c3 0xe9ffe0000783e000

def z475 : W := mkw 0xed6d34c800000000 0x04ed6d34c8000000 0xf97ff8e00000001d 0xe6f97ff8e0000000

def z476 : W := mkw 0xa819280404021000 0x00a8192804040210 0xf81ff8040c02305d 0xf6f81ff8040c0230

def z477 : W := mkw 0x579687b5a3f34e69 0x81579687b5a3f34e 0xc79e07ff83f3cfee 0xedc79e07ff83f3cf

def z478 : W := mkw 0x000041001080e804 0x00000041001080e8 0x3601c7007383fcff 0x7a3601c7007383fc

def z479 : W := mkw 0xed4d248000000000 0x04ed4d2480000000 0xc00e000000000000 0x04c00e0000000000

def z480 : W := mkw 0x450405a102e04c41 0x01450405a102e04c 0xc71e07e003e00c2e 0xecc71e07e003e00c

def z481 : W := mkw 0x0010002400220401 0x0000100024002204 0x0000000400620c40 0x080000000400620c

def z482 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3601c7007383f0dd 0x723601c7007383f0

def z483 : W := mkw 0x45361ded86e75d49 0x4145361ded86e75d 0xc71e3fff83e3fffe 0xedc71e3fff83e3ff

def z484 : W := mkw 0x0030586c1426b505 0x400030586c1426b5 0x39f1f8fc7c7fffff 0xfa39f1f8fc7c7fff

def z485 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0x3fe1fff800000033 0x023fe1fff8000000

def z486 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000023055 0x3000000000000230

def z487 : W := mkw 0xffd000276b7a04f1 0x08ffd000276b7a04 0xfff000e7fffe0ce7 0xf9fff000e7fffe0c

def z488 : W := mkw 0x452415e902e44d41 0x41452415e902e44d 0x07e007f803fc0f22 0x0807e007f803fc0f

def z489 : W := mkw 0xffc0c3137bd8eaf4 0x88ffc0c3137bd8ea 0xffe1c707fffdc0cb 0xfbffe1c707fffdc0

def z490 : W := mkw 0xed6d34c800000000 0x04ed6d34c8000000 0xcf7e3fe00000002e 0xe4cf7e3fe0000000

def z491 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x068007187393ffe2 0x18068007187393ff

def z492 : W := mkw 0x0000000000000000 0x0000000000000000 0x09e0000000000003 0xa009e00000000000

def z493 : W := mkw 0xffcde7903190ea24 0x84ffcde7903190ea 0xf68fc7187393ffff 0x7ef68fc7187393ff

def z494 : W := mkw 0x4510002502620441 0x0045100025026204 0xc71000e783e20ce6 0xe9c71000e783e20c

def z495 : W := mkw 0x001604a480230409 0x01001604a4802304 0x001e00e000000000 0x04001e00e0000000

def z496 : W := mkw 0xa80960025800a086 0x02a80960025800a0 0x3001c00070000000 0x023001c000700000

def z497 : W := mkw 0x128040003110a024 0x00128040003110a0 0x3681c0007393f0df 0x7a3681c0007393f0

def z498 : W := mkw 0xffc040037b58a0f4 0x08ffc040037b58a0 0xffe1c007fffff0df 0xfbffe1c007fffff0

def z499 : W := mkw 0xed1f2ca7ce6314cb 0x03ed1f2ca7ce6314 0xc91e38e78c600000 0x85c91e38e78c6000

def z500 : W := mkw 0x45341ded06e65d41 0x4145341ded06e65d 0x0ff03ffc0ffe3f77 0xb80ff03ffc0ffe3f

def z501 : W := mkw 0x001b6806dc03b08e 0x02001b6806dc03b0 0x001ff807fc03f0dc 0x17001ff807fc03f0

def z502 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000001800023f34 0x000000001800023f

def z503 : W := mkw 0xba89eb127d90faa6 0x82ba89eb127d90fa 0x3e81ff187f93ffff 0x7a3e81ff187f93ff

def z504 : W := mkw 0xbaf0186e6d3e15b1 0x48baf0186e6d3e15 0x39f038fc7c7e3f77 0xb839f038fc7c7e3f

def z505 : W := mkw 0x45361ded86e75d49 0x4145361ded86e75d 0xcf7e3fe78fefccee 0xedcf7e3fe78fefcc

def z506 : W := mkw 0x451604a582630449 0x01451604a5826304 0xc11e00e780620c66 0xadc11e00e780620c

def z507 : W := mkw 0x0030186c04261501 0x400030186c042615 0x097038e40c6e3055 0xb0097038e40c6e30

def z508 : W := mkw 0xa81968065c02b086 0x02a81968065c02b0 0x3811f8047c023055 0xb23811f8047c0230

def z509 : W := mkw 0xffc0c2137b58a2f4 0x88ffc0c2137b58a2 0xffe1c01ffffc33d3 0xfbffe1c01ffffc33

def z510 : W := mkw 0xffc000034a4800d0 0x08ffc000034a4800 0xffe000078c6c0003 0xe1ffe000078c6c00

def z511 : W := mkw 0xa800000000000000 0x00a8000000000000 0xf800000000000001 0xe0f8000000000000

def z512 : W := mkw 0x0010492435b6ff25 0xc00010492435b6ff 0x000000047fffffc0 0x18000000047fffff

def z513 : W := mkw 0x000000036b5800f0 0x08000000036b5800 0x09e00007fffc00c3 0xb909e00007fffc00

def z514 : W := mkw 0xed40000000000000 0x00ed400000000000 0xc960000000000000 0x80c9600000000000

def z515 : W := mkw 0xa80b6002d801a08e 0x02a80b6002d801a0 0xf00fc003f003f0dd 0x77f00fc003f003f0

def z516 : W := mkw 0x000041003190ea24 0x80000041003190ea 0x3001c0007393ffdd 0x7a3001c0007393ff

def z517 : W := mkw 0xfff61defefff5df9 0x49fff61defefff5d 0xfffe3fffffffffff 0xfdfffe3fffffffff

def z518 : W := mkw 0x003b786c9427b50f 0x42003b786c9427b5 0x001ff8f80003ff3c 0x06001ff8f80003ff

def z519 : W := mkw 0xba8be312f991eaae 0x82ba8be312f991ea 0xf68fc71bf393ffff 0x7ff68fc71bf393ff

def z520 : W := mkw 0x0030184c04061100 0x400030184c040611 0x08f0381c0c1e3355 0xb008f0381c0c1e33

def z521 : W := mkw 0xffc60583ebd948f8 0x09ffc60583ebd948 0xf60e0703f381c088 0x45f60e0703f381c0

def z522 : W := mkw 0x000041037bd8eaf4 0x88000041037bd8ea 0x00000007ffffffc0 0x1900000007ffffff

def z523 : W := mkw 0xffc041037bd8eaf4 0x88ffc041037bd8ea 0xffe00007ffffffc3 0xf9ffe00007ffffff

def z524 : W := mkw 0x0020106800240501 0x4000201068002405 0x09e000fc0c7c0f63 0xb809e000fc0c7c0f

def z525 : W := mkw 0xa83b786edc27b58f 0x42a83b786edc27b5 0xf81ff8fffc03fffd 0xf7f81ff8fffc03ff

def z526 : W := mkw 0x0010082404261501 0x4000100824042615 0x09e000040c7e3f43 0xb809e000040c7e3f

def z527 : W := mkw 0x0010080404021000 0x0000100804040210 0x081038040c000000 0x80081038040c0000

def z528 : W := mkw 0x0000c2101000a204 0x800000c2101000a2 0x0001c01800003310 0x020001c018000033

def z529 : W := mkw 0x0030186c04261501 0x400030186c042615 0x097038fc0c6e3f34 0x80097038fc0c6e3f

def z530 : W := mkw 0xffc0821000000000 0x00ffc08210000000 0xffe1c7180000003f 0xe2ffe1c718000000

def z531 : W := mkw 0x0020104800000000 0x0000201048000000 0x09f038f800123f77 0xb809f038f800123f

def z532 : W := mkw 0x0030186c04261501 0x400030186c042615 0x011038fc00623f76 0xa8011038fc00623f

def z533 : W := mkw 0x00024002d801a08e 0x0200024002d801a0 0x00000003f001c080 0x0100000003f001c0

def z534 : W := mkw 0xbaf9ba7c04261501 0x44baf9ba7c042615 0x39f1f8fc0c7e3f77 0xba39f1f8fc0c7e3f

def z535 : W := mkw 0xffcda69000000000 0x04ffcda690000000 0xffefc7000000000b 0xe6ffefc700000000

def z536 : W := mkw 0xba9bea16dc03b08e 0x02ba9bea16dc03b0 0xfe9fff1ffc03f0ff 0xf7fe9fff1ffc03f0

def z537 : W := mkw 0xed7f34ed82630449 0x05ed7f34ed826304 0xc97e38e780600000 0x85c97e38e7806000

def z538 : W := mkw 0xffc00002691800b0 0x08ffc00002691800 0xffe000007c1c0003 0xf0ffe000007c1c00

def z539 : W := mkw 0x1280c3101080ea04 0x801280c3101080ea 0x3681c7180003ff3f 0x623681c7180003ff

def z540 : W := mkw 0xfff0186f6f7e15f1 0x48fff0186f6f7e15 0xfff038e7fffc00c3 0xf9fff038e7fffc00

def z541 : W := mkw 0x0012002480230409 0x0000120024802304 0xc11e00e78063ccee 0xedc11e00e78063cc

def z542 : W := mkw 0xffdb2807ef5b10fa 0x0affdb2807ef5b10 0xfffe3807fffc00c3 0xfdfffe3807fffc00

def z543 : W := mkw 0x4506058182c14848 0x014506058182c148 0xc60e07038383ccee 0x6dc60e07038383cc

def z544 : W := mkw 0x1280831021904a20 0x801280831021904a 0x0680071803923f77 0x380680071803923f

def z545 : W := mkw 0xff9fefb7fff3feef 0x83ff9fefb7fff3fe 0xff9ffffffff3ffff 0xffff9ffffffff3ff

def z546 : W := mkw 0x0020184804041100 0x4000201848040411 0x09e0381c0c7c3353 0xb809e0381c0c7c33

def z547 : W := mkw 0x57e4d7d83190ea24 0x8457e4d7d83190ea 0x37e1c7f87393ffff 0x7a37e1c7f87393ff

def z548 : W := mkw 0x0030186c04261501 0x400030186c042615 0x09f038e40c7c0043 0xb809f038e40c7c00

def z549 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc60e070783e3ccc8 0x4dc60e070783e3cc

def z550 : W := mkw 0xffffb7fc80a34c09 0x05ffffb7fc80a34c 0xfffffff80003cc3f 0xe6fffffff80003cc

def z551 : W := mkw 0x12a0d3583190ea24 0x8012a0d3583190ea 0x3ff1fff87393ffff 0xfa3ff1fff87393ff

def z552 : W := mkw 0xa8120006c8030088 0x00a8120006c80300 0xf81e0007fc03c0cd 0xf5f81e0007fc03c0

def z553 : W := mkw 0x1280821000000000 0x0012808210000000 0x0680071800000022 0x0006800718000000

def z554 : W := mkw 0x579687b582e34c49 0x01579687b582e34c 0xf79fc7ff83e3ccff 0xeff79fc7ff83e3cc

def z555 : W := mkw 0xffedb7f902e04c41 0x05ffedb7f902e04c 0xfffffff803e00c3f 0xeefffffff803e00c

def z556 : W := mkw 0x45164da7dee3fccf 0x0345164da7dee3fc 0xc71e07e7ffe3fcee 0xfdc71e07e7ffe3fc

def z557 : W := mkw 0x5784869000000000 0x0057848690000000 0xf79fc7f80000003f 0xe6f79fc7f8000000

def z558 : W := mkw 0xffedfeda5c00b086 0x06ffedfeda5c00b0 0xfffffff87c00303f 0xf6fffffff87c0030

def z559 : W := mkw 0x1296c7b4b1b3ee2d 0x811296c7b4b1b3ee 0x369fc7f87393ffff 0x7e369fc7f87393ff

def z560 : W := mkw 0xbae9b25800000000 0x04bae9b258000000 0x3ee1ff180000003f 0x623ee1ff18000000

def z561 : W := mkw 0x4530186d06661541 0x404530186d066615 0xcff038ff8ffe3ff7 0xf9cff038ff8ffe3f

def z562 : W := mkw 0xffe9b25800000000 0x04ffe9b258000000 0xffe1f81800000013 0xe2ffe1f818000000

def z563 : W := mkw 0x0020184804041100 0x4000201848040411 0x09f038f80c1c3337 0xb009f038f80c1c33

def z564 : W := mkw 0xed5b6807de4bb0de 0x0aed5b6807de4bb0 0xf97ff807fc6ff0dd 0xf7f97ff807fc6ff0

def z565 : W := mkw 0xbac000036b5800f0 0x08bac000036b5800 0x38e00007fffc00c1 0x1938e00007fffc00

def z566 : W := mkw 0x45341cec04261501 0x4045341cec042615 0xcffe3ffc0c7e3f7f 0xfccffe3ffc0c7e3f

def z567 : W := mkw 0xbadb6806fd1bb0be 0x0abadb6806fd1bb0 0xf8fff807fc1ff0dd 0xf7f8fff807fc1ff0

def z568 : W := mkw 0xffe0184b6f5c11f0 0x48ffe0184b6f5c11 0xffe0381ffffc33d3 0xf9ffe0381ffffc33

def z569 : W := mkw 0x003b786c9427b50f 0x42003b786c9427b5 0x09fff8fc0c7fff7f 0xbe09fff8fc0c7fff

def z570 : W := mkw 0xa80960001000a004 0x00a80960001000a0 0xf81ff8007003f0dd 0xf6f81ff8007003f0

def z571 : W := mkw 0xa81b6906fd93faae 0x82a81b6906fd93fa 0xf81ff807ff93ffdd 0xfff81ff807ff93ff

def z572 : W := mkw 0x57c0000123580070 0x0857c00001235800 0xc7e0000783fc00c2 0xe9c7e0000783fc00

def z573 : W := mkw 0x0032196d86e75d49 0x410032196d86e75d 0x09f038ff8ffffff7 0xb909f038ff8fffff

def z574 : W := mkw 0x5780000123500060 0x0057800001235000 0xf7800007f3f000c3 0xf9f7800007f3f000

def z575 : W := mkw 0xa81b2806cc03108a 0x02a81b2806cc0310 0xc81e38078c03c0cc 0xe5c81e38078c03c0

def z576 : W := mkw 0xffffb6fd82630449 0x05ffffb6fd826304 0xffffffff8060003f 0xe7ffffffff806000

def z577 : W := mkw 0x0020104800000000 0x0000201048000000 0x08e0381800000011 0x0008e03818000000

def z578 : W := mkw 0x0000000248000080 0x0000000002480000 0x00000007fc0000c0 0x1100000007fc0000

def z579 : W := mkw 0xffc0c3103190ea24 0x80ffc0c3103190ea 0xffe1c7187393ffff 0xfaffe1c7187393ff

def z580 : W := mkw 0x0012000480030008 0x0000120004800300 0x000000078003c0c0 0x01000000078003c0

def z581 : W := mkw 0xa83b784edc03b08e 0x02a83b784edc03b0 0xf9fff8fffc03f0ff 0xf7f9fff8fffc03f0

def z582 : W := mkw 0x0010082404261501 0x4000100824042615 0x0080001c0c7e3f77 0x380080001c0c7e3f

def z583 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xf7000007f3e000c2 0xe9f7000007f3e000

def z584 : W := mkw 0xffd6c7b7fbfbeefd 0x89ffd6c7b7fbfbee 0xffffc7ffffffffff 0xffffffc7ffffffff

def z585 : W := mkw 0xa81b2806cc03108a 0x02a81b2806cc0310 0xf81ff8078c00001d 0xe7f81ff8078c0000

def z586 : W := mkw 0x0010082404261501 0x4000100824042615 0x081038040c7e3f55 0xb8081038040c7e3f

def z587 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xcfe000078ffc0002 0x89cfe000078ffc00

def z588 : W := mkw 0x000040001000a004 0x00000040001000a0 0x3001c00070003011 0x123001c000700030

def z589 : W := mkw 0xa81b2806cc03108a 0x02a81b2806cc0310 0xf81e3807fc0000c1 0xf5f81e3807fc0000

def z590 : W := mkw 0xbafbfa5edc03b08e 0x06bafbfa5edc03b0 0xf8fff81ffc03f0dd 0xf7f8fff81ffc03f0

def z591 : W := mkw 0x001048041402b004 0x00001048041402b0 0x3811f8047c03f0dd 0xf23811f8047c03f0

def z592 : W := mkw 0x45361ced86671549 0x4145361ced866715 0xc97e38e78c6c0000 0x85c97e38e78c6c00

def z593 : W := mkw 0x12b09a7c04261501 0x4012b09a7c042615 0x3ff1fffc0c7e3f7f 0xfa3ff1fffc0c7e3f

def z594 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xf6000007fffc00c0 0x59f6000007fffc00

def z595 : W := mkw 0x4540000102480050 0x0845400001024800 0x01600000006c0000 0x0001600000006c00

def z596 : W := mkw 0xbac0000000000000 0x00bac00000000000 0x38e0000000000001 0x0038e00000000000

def z597 : W := mkw 0x4500000102400040 0x0045000001024000 0xc600000383800080 0x41c6000003838000

def z598 : W := mkw 0x451404a400220401 0x00451404a4002204 0xc71e07e400620c6e 0xecc71e07e400620c

def z599 : W := mkw 0x00124125b3f3ee6d 0x8100124125b3f3ee 0x00000007f3f3ffc0 0x1900000007f3f3ff

def z600 : W := mkw 0xfffff7fdb3f3ee6d 0x85fffff7fdb3f3ee 0xfffffffff3f3ffff 0xfffffffffff3f3ff

def z601 : W := mkw 0xed5b2807ce4b10da 0x0aed5b2807ce4b10 0xc97e38078c6c0000 0x85c97e38078c6c00

def z602 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xf6800003f39000c3 0x79f6800003f39000

def z603 : W := mkw 0x0020104800000000 0x0000201048000000 0x01e000f800000022 0x0001e000f8000000

def z604 : W := mkw 0x5784c7b133f0ee65 0x815784c7b133f0ee 0x3781c7f873f3ffff 0x7a3781c7f873f3ff

def z605 : W := mkw 0xffedb6f800240501 0x44ffedb6f8002405 0xfffffff8007c0f3f 0xeefffffff8007c0f

def z606 : W := mkw 0x5780c31133d0ea64 0x805780c31133d0ea 0xf781c71ff3f3ffff 0xfbf781c71ff3f3ff

def z607 : W := mkw 0x0020104800000000 0x0000201048000000 0x097038e000000000 0x80097038e0000000

def z608 : W := mkw 0x001b28048403100a 0x02001b2804840310 0x001e380000000000 0x04001e3800000000

def z609 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0x070007e783e3cce2 0x09070007e783e3cc

def z610 : W := mkw 0xffe0104800000000 0x00ffe01048000000 0xfff038f800000037 0xe0fff038f8000000

def z611 : W := mkw 0x57d605a5a3fb4c79 0x0957d605a5a3fb4c 0xc7fe07e783ffccee 0xedc7fe07e783ffcc

def z612 : W := mkw 0x4506048182410048 0x0145060481824100 0xc00e000380000000 0x05c00e0003800000

def z613 : W := mkw 0x579605a5a3f34c69 0x01579605a5a3f34c 0xf79e07e7f3f3ccef 0xfdf79e07e7f3f3cc

def z614 : W := mkw 0x0010082404261501 0x4000100824042615 0x011000e40c7e3f66 0xb8011000e40c7e3f

def z615 : W := mkw 0x12b0da7c3536b725 0xc012b0da7c3536b7 0x39f1f8fc7c7e3f77 0xba39f1f8fc7c7e3f

def z616 : W := mkw 0x57c0000123580070 0x0857c00001235800 0x37e0000073fc00c3 0x7837e0000073fc00

def z617 : W := mkw 0x0000000021100020 0x0000000000211000 0x00000000739000c0 0x1800000000739000

def z618 : W := mkw 0xed4000034a4800d0 0x08ed4000034a4800 0xc000000380000000 0x01c0000003800000

def z619 : W := mkw 0xffeff6dad801a08e 0x06ffeff6dad801a0 0xfffffffbf001c0bf 0xe7fffffffbf001c0

def z620 : W := mkw 0x1280831021904a20 0x801280831021904a 0x0600070003800000 0x0006000700038000

def z621 : W := mkw 0x1280000021100020 0x0012800000211000 0x3680001873923ff7 0x783680001873923f

def z622 : W := mkw 0x00120806cc03108a 0x0200120806cc0310 0x000000078c000000 0x01000000078c0000

def z623 : W := mkw 0x00361dec84a75d09 0x4100361dec84a75d 0x001e3ff80003ff3c 0x04001e3ff80003ff

def z624 : W := mkw 0xa83b786edc27b58f 0x42a83b786edc27b5 0xf97ff8e7fc6ff0dd 0xf7f97ff8e7fc6ff0

def z625 : W := mkw 0xa829784a5c04b186 0x42a829784a5c04b1 0x38e1f8187c1c3311 0x1238e1f8187c1c33

def z626 : W := mkw 0x000405a000a04c01 0x01000405a000a04c 0x000007e000000c20 0x00000007e000000c

def z627 : W := mkw 0xa809200000000000 0x00a8092000000000 0x3801f80000000011 0x023801f800000000

def z628 : W := mkw 0xffdb6807ff5bb0fe 0x0affdb6807ff5bb0 0xfe1ff807ff83f0dd 0xf7fe1ff807ff83f0

def z629 : W := mkw 0xa81b6906dc83f88e 0x02a81b6906dc83f8 0xfe1fff07ff83fcff 0xfffe1fff07ff83fc

def z630 : W := mkw 0x1280000021100020 0x0012800000211000 0x0680000003900002 0x0806800000039000

def z631 : W := mkw 0x0012080484031008 0x0000120804840310 0xc81e38078c03f0dd 0xf5c81e38078c03f0

def z632 : W := mkw 0x57e496d800000000 0x0457e496d8000000 0x37e1c7f80000003f 0x6237e1c7f8000000

def z633 : W := mkw 0x57c4869000000000 0x0457c48690000000 0x0600070000000000 0x0006000700000000

def z634 : W := mkw 0xa869304800000000 0x04a8693048000000 0x0860380000000000 0x0008603800000000

def z635 : W := mkw 0xa80040025800a084 0x00a80040025800a0 0xf801c007fc03f0dd 0xf3f801c007fc03f0

def z636 : W := mkw 0x0012012582e34c49 0x010012012582e34c 0x0600070783e3ccee 0x690600070783e3cc

def z637 : W := mkw 0x453615ed82e74d49 0x41453615ed82e74d 0xc7fe07ff83ffcfee 0xedc7fe07ff83ffcf

def z638 : W := mkw 0x1290cb3435b6ff25 0xc01290cb3435b6ff 0x3681c71c7fffffff 0x7a3681c71c7fffff

def z639 : W := mkw 0xffc0000021100020 0x00ffc00000211000 0xffe00000739000c3 0xf8ffe00000739000

def z640 : W := mkw 0x1280c2103110a224 0x801280c2103110a2 0x3081c0187013f3dd 0x723081c0187013f3

def z641 : W := mkw 0x1280010021904820 0x0012800100219048 0x368007007393ccef 0x78368007007393cc

def z642 : W := mkw 0x451405a502e24c41 0x01451405a502e24c 0x071007e403e20c66 0xa8071007e403e20c

def z643 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0x3801f807fc03f0d1 0x133801f807fc03f0

def z644 : W := mkw 0x57e496f800240501 0x4457e496f8002405 0x07e007f8007c0f22 0x0807e007f8007c0f

def z645 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3681c7187391f399 0x523681c7187391f3

def z646 : W := mkw 0x0010002400220401 0x0000100024002204 0x001000e000020c24 0x00001000e000020c

def z647 : W := mkw 0x12a0db583594fb24 0xc012a0db583594fb 0x3ee1ff187f9fffff 0x7a3ee1ff187f9fff

def z648 : W := mkw 0xa81b6006d803a08e 0x02a81b6006d803a0 0xf01fc007f003c0cc 0xe7f01fc007f003c0

def z649 : W := mkw 0xa81f6da6dca3fc8f 0x03a81f6da6dca3fc 0xf81fffe7fc03fcfd 0xf7f81fffe7fc03fc

def z650 : W := mkw 0x000041003190ea24 0x80000041003190ea 0x008000187393fff7 0x38008000187393ff

def z651 : W := mkw 0x0012012582e34c49 0x010012012582e34c 0x011000e783e3cce6 0xa9011000e783e3cc

def z652 : W := mkw 0x450405a102e04c41 0x01450405a102e04c 0x070007e003e3ccee 0x68070007e003e3cc

def z653 : W := mkw 0x000040001000a004 0x00000040001000a0 0x000000007003f0c0 0x10000000007003f0

def z654 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3601c7007393ffc8 0x5a3601c7007393ff

def z655 : W := mkw 0xed0f6583dac1e8ce 0x03ed0f6583dac1e8 0xf60fc703f381c088 0x47f60fc703f381c0

def z656 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0x071e07e003e3cc2e 0x0c071e07e003e3cc

def z657 : W := mkw 0x129beb14b593fa2e 0x82129beb14b593fa 0x369fff187393ffff 0x7e369fff187393ff

def z658 : W := mkw 0xed7f3ccecc03108a 0x06ed7f3ccecc0310 0xc97e38e78c000000 0x85c97e38e78c0000

def z659 : W := mkw 0x57f49efc04261501 0x4457f49efc042615 0x0ff03ffc0c7e3f77 0xb80ff03ffc0c7e3f

def z660 : W := mkw 0xffcda69000000000 0x04ffcda690000000 0xf71fc7e00000002e 0xe6f71fc7e0000000

def z661 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3681c7187391cfaa 0x4a3681c7187391cf

def z662 : W := mkw 0x0030196c04a65d01 0x400030196c04a65d 0x0ff03ffc0fffffff 0xf80ff03ffc0fffff

def z663 : W := mkw 0x12b0186c25361521 0x4012b0186c253615 0x3ff038fc7ffe3ff7 0xf83ff038fc7ffe3f

def z664 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080000000100043 0x3800800000001000

def z665 : W := mkw 0x0010082404261501 0x4000100824042615 0x000000040c6c0000 0x00000000040c6c00

def z666 : W := mkw 0x0000000000000000 0x0000000000000000 0x08e000000c1c0001 0x1008e000000c1c00

def z667 : W := mkw 0xed1f6d87dec3f8ce 0x03ed1f6d87dec3f8 0xfe1fff07ff83f0dd 0xf7fe1fff07ff83f0

def z668 : W := mkw 0xa83b386ecc27158b 0x42a83b386ecc2715 0xc97e38e78c6c0000 0x85c97e38e78c6c00

def z669 : W := mkw 0x0020106800240501 0x4000201068002405 0x01e000f8007e3f77 0x3801e000f8007e3f

def z670 : W := mkw 0x57e497d821904a20 0x8457e497d821904a 0x07e007f803900f22 0x0807e007f803900f

def z671 : W := mkw 0x4500000000000000 0x0045000000000000 0xc700000000000002 0xe0c7000000000000

def z672 : W := mkw 0xfff0db7f7ffefff5 0xc8fff0db7f7ffeff 0xfff1ffffffffffff 0xfbfff1ffffffffff

def z673 : W := mkw 0x0000000000000000 0x0000000000000000 0x0100000400600042 0xa801000004006000

def z674 : W := mkw 0x001b68049403b00e 0x02001b68049403b0 0x081ff8040c03f05d 0xb6081ff8040c03f0

def z675 : W := mkw 0x0000000000000000 0x0000000000000000 0x3001c0000000001d 0x623001c000000000

def z676 : W := mkw 0x001b68049403b00e 0x02001b68049403b0 0xc01ff8078003f0dc 0xe7c01ff8078003f0

def z677 : W := mkw 0x0010080404021000 0x0000100804040210 0x0010380000023014 0x0000103800000230

def z678 : W := mkw 0xed7d3cec04261501 0x44ed7d3cec042615 0xc97e38e40c6c0000 0x84c97e38e40c6c00

def z679 : W := mkw 0x0000000102400040 0x0000000001024000 0x0000000783e000c0 0x090000000783e000

def z680 : W := mkw 0x0000002000200401 0x0000000020002004 0x010000e000600c22 0x08010000e000600c

def z681 : W := mkw 0xbac0c2127918a2b4 0x88bac0c2127918a2 0x38e1c0187c1c3311 0x1238e1c0187c1c33

def z682 : W := mkw 0x000000034a4800d0 0x08000000034a4800 0x000000078c6c0000 0x01000000078c6c00

def z683 : W := mkw 0xffcde7903190ea24 0x84ffcde7903190ea 0xf60fc7007381c088 0x46f60fc7007381c0

def z684 : W := mkw 0x4504058000804800 0x0045040580008048 0xc71e07e00383ccee 0xecc71e07e00383cc

def z685 : W := mkw 0x0012010480834808 0x0000120104808348 0xc61e07078383ccee 0xedc61e07078383cc

def z686 : W := mkw 0xbac968027d18b0b6 0x0abac968027d18b0 0x38e1f8007c1c3011 0x1238e1f8007c1c30

def z687 : W := mkw 0xa800000248000080 0x00a8000002480000 0xf9e00007fc7c00c3 0xf9f9e00007fc7c00

def z688 : W := mkw 0x001b68049403b00e 0x02001b68049403b0 0x301ff8007003f0dd 0x76301ff8007003f0

def z689 : W := mkw 0xa80968025c00b086 0x02a80968025c00b0 0xf801f807fc0030d1 0xf3f801f807fc0030

def z690 : W := mkw 0xbae9f3583190ea24 0x84bae9f3583190ea 0x3ee1ff187393ffff 0x7a3ee1ff187393ff

def z691 : W := mkw 0x1280c3137bd8eaf4 0x881280c3137bd8ea 0x3681c71fffffffff 0x7b3681c71fffffff

def z692 : W := mkw 0x0016c7b490a3ee0d 0x810016c7b490a3ee 0x001fc7f80003ff3c 0x06001fc7f80003ff

def z693 : W := mkw 0x12b09b7c25b65f21 0xc012b09b7c25b65f 0x0ff03ffc0ffe3f77 0xb80ff03ffc0ffe3f

def z694 : W := mkw 0x00361dec84a75d09 0x4100361dec84a75d 0x09fe3ffc0c7fff7f 0xbc09fe3ffc0c7fff

def z695 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080001800100f22 0x080080001800100f

def z696 : W := mkw 0x0000c3101080ea04 0x800000c3101080ea 0x3001c7187003fffd 0x723001c7187003ff

def z697 : W := mkw 0x45361ced86671549 0x4145361ced866715 0xc9fe38ff8c7e3f77 0xbdc9fe38ff8c7e3f

def z698 : W := mkw 0xffc083136bd84af0 0x88ffc083136bd84a 0xffe0071ffffc0fe3 0xf9ffe0071ffffc0f

def z699 : W := mkw 0x451645a5b3f3ee6d 0x81451645a5b3f3ee 0xc71e07e7f3f3ffee 0xfdc71e07e7f3f3ff

def z700 : W := mkw 0x1280831021904a20 0x801280831021904a 0x068007180393cfee 0x68068007180393cf

def z701 : W := mkw 0x57e497f902e04c41 0x0557e497f902e04c 0x07e007f803e00c22 0x0807e007f803e00c

def z702 : W := mkw 0x00124806dc03b08e 0x0200124806dc03b0 0x3001c007fc03f0dd 0x733001c007fc03f0

def z703 : W := mkw 0x12c0000021180030 0x0812c00000211800 0x00e00000001c0000 0x0000e00000001c00

def z704 : W := mkw 0x0030186c04261501 0x400030186c042615 0x09f038fc0c7c3311 0x9009f038fc0c7c33

def z705 : W := mkw 0x000048025c00b086 0x02000048025c00b0 0x000000007c003000 0x10000000007c0030

def z706 : W := mkw 0xffcb6003fb59a0fe 0x0affcb6003fb59a0 0xf60fc003f381c088 0x47f60fc003f381c0

def z707 : W := mkw 0x45261dc986c55948 0x4145261dc986c559 0xceee3f1b8f9df399 0x55ceee3f1b8f9df3

def z708 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xf7e00007fffc00c2 0x59f7e00007fffc00

def z709 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xfffffff87ffc003f 0xfefffffff87ffc00

def z710 : W := mkw 0xffedb6d821100220 0x84ffedb6d8211002 0xfffffff80010033f 0xe6fffffff8001003

def z711 : W := mkw 0xa81b6826dc23b48f 0x02a81b6826dc23b4 0xf9fff8e7fc7ffcff 0xfff9fff8e7fc7ffc

def z712 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3e91ff187393ffff 0xfa3e91ff187393ff

def z713 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xcf1e3fe783e3ccff 0xedcf1e3fe783e3cc

def z714 : W := mkw 0xffedb6d923580070 0x0cffedb6d9235800 0xfffffff80380003f 0xe6fffffff8038000

def z715 : W := mkw 0xffc404836b5800f0 0x08ffc404836b5800 0xfffe00e7fffc00c3 0xfdfffe00e7fffc00

def z716 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf81ff807fc03f0c8 0xd7f81ff807fc03f0

def z717 : W := mkw 0x450605a182e14c49 0x01450605a182e14c 0xc60e07e38381cca8 0x45c60e07e38381cc

def z718 : W := mkw 0x0012012480a34c09 0x000012012480a34c 0xc71e07e783e3ccee 0xedc71e07e783e3cc

def z719 : W := mkw 0xffc082136b5802f0 0x88ffc082136b5802 0xffe0001ffffc03c3 0xf9ffe0001ffffc03

def z720 : W := mkw 0xed4000036b5800f0 0x08ed4000036b5800 0xcf600007fffc00c2 0xf9cf600007fffc00

def z721 : W := mkw 0xffcda6936b5800f0 0x0cffcda6936b5800 0xffffc7e7fffc00ef 0xffffffc7e7fffc00

def z722 : W := mkw 0xa80b6002d801a08e 0x02a80b6002d801a0 0xf80ff803f001c099 0x47f80ff803f001c0

def z723 : W := mkw 0x002db6d800000000 0x04002db6d8000000 0x009ffff80000003f 0x26009ffff8000000

def z724 : W := mkw 0xffedb6db4a4800d0 0x0cffedb6db4a4800 0xffffffff8fec00ff 0xefffffffff8fec00

def z725 : W := mkw 0xbae9fa5a7d18b0b6 0x0ebae9fa5a7d18b0 0x38e1f8187c1c3011 0x1238e1f8187c1c30

def z726 : W := mkw 0xa80b6802dc01b08e 0x02a80b6802dc01b0 0xf80ff803fc03f0dd 0x77f80ff803fc03f0

def z727 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xffe00007fffc0003 0x99ffe00007fffc00

def z728 : W := mkw 0xffcde7937bd8eaf4 0x8cffcde7937bd8ea 0xf60fc703f381c088 0x47f60fc703f381c0

def z729 : W := mkw 0xbad605a6e9bb4cb9 0x09bad605a6e9bb4c 0x38fe07e07c1fcc2d 0x1438fe07e07c1fcc

def z730 : W := mkw 0x57c000036b5800f0 0x0857c000036b5800 0x0fe00007fffc00c3 0xb90fe00007fffc00

def z731 : W := mkw 0x57e497f923f04e61 0x8557e497f923f04e 0x07e007f803f00f22 0x0807e007f803f00f

def z732 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffff80c1c003f 0xf6fffffff80c1c00

def z733 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xcf1e07e78fe3ccef 0xfdcf1e07e78fe3cc

def z734 : W := mkw 0x002db6d800000000 0x04002db6d8000000 0x01fffff80000003e 0x0601fffff8000000

def z735 : W := mkw 0xffcda69000000000 0x04ffcda690000000 0xff1fffe00000003f 0xe6ff1fffe0000000

def z736 : W := mkw 0xed0d6da35ee0fcc7 0x03ed0d6da35ee0fc 0x3f01ffe07fe03c33 0x1a3f01ffe07fe03c

def z737 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc79e07ff83f3cfee 0xedc79e07ff83f3cf

def z738 : W := mkw 0xffedb6d821100020 0x04ffedb6d8211000 0xfffffffc7ffc00ff 0xfefffffffc7ffc00

def z739 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3681c71c7fffffff 0x7a3681c71c7fffff

def z740 : W := mkw 0xffedb6da48000080 0x04ffedb6da480000 0xffffffff8c00003f 0xe7ffffffff8c0000

def z741 : W := mkw 0xed40c3135ac8ead4 0x88ed40c3135ac8ea 0xc961c71f8c6fff3c 0x83c961c71f8c6fff

def z742 : W := mkw 0x12b0db7c35b6ff25 0xc012b0db7c35b6ff 0x3f71ffe47fedc088 0xc23f71ffe47fedc0

def z743 : W := mkw 0x455605a582eb4c59 0x09455605a582eb4c 0xc77e07e783efccee 0xedc77e07e783efcc

def z744 : W := mkw 0xbafbb37d82e34c49 0x05bafbb37d82e34c 0x38e1f81f83e3ccd1 0x0b38e1f81f83e3cc

def z745 : W := mkw 0xa80b6002d801a08e 0x02a80b6002d801a0 0xf01ff803f001c09c 0x47f01ff803f001c0

def z746 : W := mkw 0x00124926fdb7ffaf 0xc200124926fdb7ff 0x00000007ffffffc0 0x1900000007ffffff

def z747 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xf61ffffbf38000bc 0x47f61ffffbf38000

def z748 : W := mkw 0x0030186c04261501 0x400030186c042615 0x09f038fc0c7e3f35 0x9009f038fc0c7e3f

def z749 : W := mkw 0xed0d24834a4000c0 0x00ed0d24834a4000 0xff1fffe7ffe000ff 0xffff1fffe7ffe000

def z750 : W := mkw 0x002db6d800000000 0x04002db6d8000000 0x001fffe000000008 0x06001fffe0000000

def z751 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf01ff803f001c088 0x47f01ff803f001c0

def z752 : W := mkw 0xed0000034a4000c0 0x00ed0000034a4000 0xffe00007fffc00c3 0xf9ffe00007fffc00

def z753 : W := mkw 0xbae9fa5a7d10b2a6 0x86bae9fa5a7d10b2 0x38e1f8187c103311 0x1238e1f8187c1033

def z754 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xffe00007fffe30d7 0xf9ffe00007fffe30

def z755 : W := mkw 0xffd24927fffbfcff 0x0bffd24927fffbfc 0xffe00007fffffcc3 0xf9ffe00007fffffc

def z756 : W := mkw 0xffedb6d923580070 0x0cffedb6d9235800 0xfffffff873fc00ff 0xfefffffff873fc00

def z757 : W := mkw 0xffedb6db4a4800d0 0x0cffedb6db4a4800 0xfffffffb8000003f 0xe7fffffffb800000

def z758 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xcffffff80000003e 0x86cffffff8000000

def z759 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e3cce2 0x8dc71e07e783e3cc

def z760 : W := mkw 0xbae9f25a7918a2b4 0x8cbae9f25a7918a2 0x38e1f8187c1c3311 0x1238e1f8187c1c33

def z761 : W := mkw 0xffcd24836b5800f0 0x08ffcd24836b5800 0xffffffe7fffc00ff 0xffffffffe7fffc00

def z762 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xffffffffffec00bf 0xe7ffffffffffec00

def z763 : W := mkw 0xa81b6006d803a08e 0x02a81b6006d803a0 0xf81ff807f003c0dd 0xe7f81ff807f003c0

def z764 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xfffffffff3e000ff 0xeffffffffff3e000

def z765 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xffffffe7fffc00cb 0xffffffffe7fffc00

def z766 : W := mkw 0x0012492596e3fc4f 0x030012492596e3fc 0x0000000783e3fcc0 0x090000000783e3fc

def z767 : W := mkw 0x57e497f923f84c71 0x0d57e497f923f84c 0x07e007f803fc0c22 0x0807e007f803fc0c

def z768 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xff7ffff80000003c 0xc6ff7ffff8000000

def z769 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xffffffff8ffc003f 0xefffffffff8ffc00

def z770 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xffe0001ffffc00f7 0xf9ffe0001ffffc00

def z771 : W := mkw 0xffedb6d821100020 0x04ffedb6d8211000 0xfffffff87010003f 0xf6fffffff8701000

def z772 : W := mkw 0xba9bab16ed935aaa 0x82ba9bab16ed935a 0xce9e3f1f8f900f22 0x8dce9e3f1f8f900f

def z773 : W := mkw 0xed6d75c83190ea24 0x84ed6d75c83190ea 0xc97e38e07393ffc0 0x9cc97e38e07393ff

def z774 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e3fcff 0xfdc71e07e783e3fc

def z775 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0x3fe00007fffc00c3 0x193fe00007fffc00

def z776 : W := mkw 0xa82db6da48000080 0x04a82db6da480000 0xf81ffffffc0000fd 0xf7f81ffffffc0000

def z777 : W := mkw 0xffcd24836b5800f0 0x0cffcd24836b5800 0xffee0007fffc00c3 0xfdffee0007fffc00

def z778 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf91ff807fc63f0df 0xfff91ff807fc63f0

def z779 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc70e07e783e3ccea 0x4dc70e07e783e3cc

def z780 : W := mkw 0x0032186c84271509 0x400032186c842715 0x09f038ff8c7ffff7 0xb909f038ff8c7fff

def z781 : W := mkw 0x45160da586e75d49 0x4145160da586e75d 0xcffe07e78fffffef 0xfdcffe07e78fffff

def z782 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffff80002307f 0xf6fffffff8000230

def z783 : W := mkw 0xa82b706ad825a58f 0x42a82b706ad825a5 0xf1efc0fbf07dcfaa 0x4ff1efc0fbf07dcf

def z784 : W := mkw 0xffedb6da48000080 0x04ffedb6da480000 0xfffffffffc7c00ff 0xfffffffffffc7c00

def z785 : W := mkw 0xed4000036b5800f0 0x08ed4000036b5800 0xf9600007fffc00c1 0xf9f9600007fffc00

def z786 : W := mkw 0x0020186804241501 0x4000201868042415 0x09f038f80c7c3f37 0xb809f038f80c7c3f

def z787 : W := mkw 0xffedb6da48000080 0x04ffedb6da480000 0xfffffff87c00003f 0xf6fffffff87c0000

def z788 : W := mkw 0x57edb6d800000000 0x0457edb6d8000000 0x0ffffff80000003f 0xa60ffffff8000000

def z789 : W := mkw 0xa80b6002d801a08e 0x02a80b6002d801a0 0xf81ff807fc01c0dd 0xf7f81ff807fc01c0

def z790 : W := mkw 0x0020186804241501 0x4000201868042415 0x09e038fc0c7c3f73 0xb809e038fc0c7c3f

def z791 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf81ff807fc13ffdd 0xfff81ff807fc13ff

def z792 : W := mkw 0xffedb6d821100020 0x04ffedb6d8211000 0xfffffff873923fff 0xfefffffff873923f

def z793 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xffffffff800000ff 0xe7ffffffff800000

def z794 : W := mkw 0x57c000036b5800f0 0x0857c000036b5800 0xc7e00007fffc00c2 0xf9c7e00007fffc00

def z795 : W := mkw 0x57f6dededc03b08e 0x0657f6dededc03b0 0x07e007fffc03f0e2 0x1107e007fffc03f0

def z796 : W := mkw 0xffc9a2136b5800f0 0x08ffc9a2136b5800 0xffffff1ffffc00ff 0xffffffff1ffffc00

def z797 : W := mkw 0xffedb6da691000a0 0x04ffedb6da691000 0xffffffffff9000ff 0xffffffffffff9000

def z798 : W := mkw 0xffedb6d902400040 0x04ffedb6d9024000 0xffffffff8060003f 0xe7ffffffff806000

def z799 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xcffe07ff8fffffff 0xfdcffe07ff8fffff

def z800 : W := mkw 0x12adb6d821100020 0x0412adb6d8211000 0x369ffff8739000ff 0x7e369ffff8739000

def z801 : W := mkw 0xa80b6002d801a08e 0x02a80b6002d801a0 0xf81ff803f001c088 0xc7f81ff803f001c0

def z802 : W := mkw 0xed2d34c800000000 0x00ed2d34c8000000 0xfffffff80000003f 0xe6fffffff8000000

def z803 : W := mkw 0xffedb6da691800b0 0x0cffedb6da691800 0xfffffffffc1c00ff 0xf7fffffffffc1c00

def z804 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffff800000019 0xc6fffffff8000000

def z805 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffff80010333f 0xf6fffffff8001033

def z806 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf81ff807fc7ff0dd 0xfff81ff807fc7ff0

def z807 : W := mkw 0x4516048582430048 0x0045160485824300 0xc71e07e783e3c0ee 0xedc71e07e783e3c0

def z808 : W := mkw 0xa81b6826dc23b48f 0x02a81b6826dc23b4 0xf81ff807fc63fcdd 0xfff81ff807fc63fc

def z809 : W := mkw 0x0032186c84271509 0x400032186c842715 0x09fe38fc0c7fff7f 0xbc09fe38fc0c7fff

def z810 : W := mkw 0x452db6d902400040 0x04452db6d9024000 0xc71fffff83e000fe 0xefc71fffff83e000

def z811 : W := mkw 0xffedb6da48000080 0x04ffedb6da480000 0xfffffffbf00000bf 0xe7fffffffbf00000

def z812 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xfffffffffc7c003f 0xf7fffffffffc7c00

def z813 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xcfe00007fffc00c2 0x99cfe00007fffc00

def z814 : W := mkw 0xa81b6806dc07b18e 0x42a81b6806dc07b1 0xf81ff807fc1ff3dd 0xf7f81ff807fc1ff3

def z815 : W := mkw 0x450605a182e14c49 0x01450605a182e14c 0xc70e07e783e1ccea 0xedc70e07e783e1cc

def z816 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffff80003c0ff 0xe6fffffff80003c0

def z817 : W := mkw 0x45160da586e35c49 0x0145160da586e35c 0xc71e07e78fe3fcee 0xfdc71e07e78fe3fc

def z818 : W := mkw 0x451605a582e74d49 0x41451605a582e74d 0xc71e07e783ffcfee 0xedc71e07e783ffcf

def z819 : W := mkw 0xa81b6826dc27b58f 0x42a81b6826dc27b5 0xf81ff807fc03ffdd 0xf7f81ff807fc03ff

def z820 : W := mkw 0xffc082136b5800f0 0x08ffc082136b5800 0xffe1c71ffffe3fff 0xfbffe1c71ffffe3f

def z821 : W := mkw 0xffedb6d902400040 0x04ffedb6d9024000 0xfffffff803e0003f 0xeefffffff803e000

def z822 : W := mkw 0x0036dffc94a7ff0d 0xc10036dffc94a7ff 0x001ffff80003ff3c 0x06001ffff80003ff

def z823 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xfff03807fffc00d7 0xf9fff03807fffc00

def z824 : W := mkw 0x45160da586e75d49 0x4145160da586e75d 0xc71e07e783e3ffee 0xedc71e07e783e3ff

def z825 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0xf681c71ff393ffff 0xfbf681c71ff393ff

def z826 : W := mkw 0x002db6db6b5800f0 0x0c002db6db6b5800 0x001ffffffffc00fc 0x1f001ffffffffc00

def z827 : W := mkw 0x128000036b5800f0 0x08128000036b5800 0x3fe00007fffc00c3 0xf93fe00007fffc00

def z828 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3681c7187393ffbd 0x523681c7187393ff

def z829 : W := mkw 0x4506058182c14848 0x014506058182c148 0xc71e07e783e1c0ee 0xedc71e07e783e1c0

def z830 : W := mkw 0xbac000036b5800f0 0x08bac000036b5800 0x3ee00007fffc00c3 0x793ee00007fffc00

def z831 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf89ff807fc13f0df 0xfff89ff807fc13f0

def z832 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xf69ffff80000003f 0x66f69ffff8000000

def z833 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3fe1c7187393ffff 0xfa3fe1c7187393ff

def z834 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xffe00007ffffc0cf 0xf9ffe00007ffffc0

def z835 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xf71fc7e783e3ccff 0xeff71fc7e783e3cc

def z836 : W := mkw 0x002db6d800000000 0x04002db6d8000000 0x081ffff80000003d 0xa6081ffff8000000

def z837 : W := mkw 0x0030186c04261501 0x400030186c042615 0x0ff03ffc0c7e3f7f 0xf80ff03ffc0c7e3f

def z838 : W := mkw 0xffedb6d923580070 0x0cffedb6d9235800 0xffffffff83fc00ff 0xefffffffff83fc00

def z839 : W := mkw 0x12c000036b5800f0 0x0812c000036b5800 0x00e00007fffc00c0 0x1900e00007fffc00

def z840 : W := mkw 0x003f7dec94a7fd0f 0x43003f7dec94a7fd 0x001ffff80003ff3c 0x06001ffff80003ff

def z841 : W := mkw 0xffc082136b5800f0 0x08ffc082136b5800 0xffe0071ffffc00e3 0xf9ffe0071ffffc00

def z842 : W := mkw 0x0030186c04261501 0x400030186c042615 0x09f038fc0c7fffff 0xf809f038fc0c7fff

def z843 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffff8700000ff 0xf6fffffff8700000

def z844 : W := mkw 0x001248049403b00c 0x00001248049403b0 0xf81ff807fc03f0dd 0xf7f81ff807fc03f0

def z845 : W := mkw 0xbaa9fa5a7d14b3a6 0xc2baa9fa5a7d14b3 0x38e1f8187c1c3311 0x1238e1f8187c1c33

def z846 : W := mkw 0x12adb6d800000000 0x0412adb6d8000000 0x309ffff80000003d 0x06309ffff8000000

def z847 : W := mkw 0x4506058182c14848 0x014506058182c148 0xc61e07e38381c0ac 0x45c61e07e38381c0

def z848 : W := mkw 0xed6db6d800000000 0x04ed6db6d8000000 0xc9fffff80000003f 0xa6c9fffff8000000

def z849 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xfffffffbf3fc00bf 0xeffffffffbf3fc00

def z850 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf81ff807fc01c0c9 0xf7f81ff807fc01c0

def z851 : W := mkw 0xffc486936b5800f0 0x08ffc486936b5800 0xffffc7fffffc00ff 0xffffffc7fffffc00

def z852 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf81ff807fc01f099 0xd7f81ff807fc01f0

def z853 : W := mkw 0x450605a182e14c49 0x01450605a182e14c 0xc70e07e383e3ccee 0x6dc70e07e383e3cc

def z854 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffff800020c7f 0xeefffffff800020c

def z855 : W := mkw 0x57edb6d800000000 0x0457edb6d8000000 0xc7fffff80000003e 0xe6c7fffff8000000

def z856 : W := mkw 0xa81b6826dc27b58f 0x42a81b6826dc27b5 0xf9fff807fc7fffdf 0xfff9fff807fc7fff

def z857 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3681c7187393ffea 0x5a3681c7187393ff

def z858 : W := mkw 0xfff0186f6f7e15f1 0x48fff0186f6f7e15 0xf61038fbf3823fb4 0x41f61038fbf3823f

def z859 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf81ff807fc03f0d1 0x97f81ff807fc03f0

def z860 : W := mkw 0xa80960025800a084 0x00a80960025800a0 0xf81ff807fc03f0dd 0xf7f81ff807fc03f0

def z861 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf81ff807fc01c09d 0xe7f81ff807fc01c0

def z862 : W := mkw 0x4516058582c34848 0x014516058582c348 0xc71e07e78383c0ee 0xe5c71e07e78383c0

def z863 : W := mkw 0x4504058102c04840 0x004504058102c048 0xc71e07e783e3ccee 0xedc71e07e783e3cc

def z864 : W := mkw 0x5780000123500060 0x0057800001235000 0xffe00007fffc00c3 0xf9ffe00007fffc00

def z865 : W := mkw 0xa81b6826dc23b48f 0x02a81b6826dc23b4 0xf99ff8fffc73ffff 0xfff99ff8fffc73ff

def z866 : W := mkw 0x001b68049403b00e 0x02001b68049403b0 0xf01ff807f003f0dd 0xf7f01ff807f003f0

def z867 : W := mkw 0xffc9a2136b5800f0 0x0cffc9a2136b5800 0xffe1c007fffc00c3 0xfbffe1c007fffc00

def z868 : W := mkw 0xffedb6db4a4800d0 0x0cffedb6db4a4800 0xfffffffffc6c00ff 0xf7fffffffffc6c00

def z869 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf81ff81ffc03fffd 0xf7f81ff81ffc03ff

def z870 : W := mkw 0x002db6d800000000 0x04002db6d8000000 0xc01ffff80000003c 0xe6c01ffff8000000

def z871 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc61e07e38383ccee 0x6dc61e07e38383cc

def z872 : W := mkw 0x452db6d800000000 0x04452db6d8000000 0xcffffff80000003f 0xe6cffffff8000000

def z873 : W := mkw 0xffedb6d821100020 0x04ffedb6d8211000 0xfffffff8738000bf 0xe6fffffff8738000

def z874 : W := mkw 0x12adb6d800000000 0x0412adb6d8000000 0x069ffff80000003e 0x06069ffff8000000

def z875 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xffe00707fffc00ef 0xf9ffe00707fffc00

def z876 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xf9e00007fffc00c1 0x99f9e00007fffc00

def z877 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xf61fffe000000008 0x46f61fffe0000000

def z878 : W := mkw 0x57adb6d800000000 0x0457adb6d8000000 0xf79ffff80000003f 0xe6f79ffff8000000

def z879 : W := mkw 0x452db6d800000000 0x04452db6d8000000 0x071ffff80000003e 0x06071ffff8000000

def z880 : W := mkw 0xffc082136b5800f0 0x08ffc082136b5800 0xffe1c01ffffc00d3 0xfbffe1c01ffffc00

def z881 : W := mkw 0x001605a480a34c09 0x01001605a480a34c 0xc61e07e78383ccee 0xedc61e07e78383cc

def z882 : W := mkw 0x57db6805b75bb07e 0x0a57db6805b75bb0 0x07fff80003fff01e 0x0e07fff80003fff0

def z883 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xff7fffe00000001d 0xe6ff7fffe0000000

def z884 : W := mkw 0x000000036b5800f0 0x08000000036b5800 0x09600007fffc00c0 0x9909600007fffc00

def z885 : W := mkw 0xffc920036b5800f0 0x08ffc920036b5800 0xffefc007fffc00cb 0xffffefc007fffc00

def z886 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e3ccac 0xc5c71e07e783e3cc

def z887 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07ff83e3fffe 0xedc71e07ff83e3ff

def z888 : W := mkw 0x452db6d800000000 0x04452db6d8000000 0xc11ffff80000003c 0x86c11ffff8000000

def z889 : W := mkw 0xbaedb6d800000000 0x04baedb6d8000000 0x39fffff80000003f 0xa639fffff8000000

def z890 : W := mkw 0x5796c6b5b373a66d 0x815796c6b5b373a6 0xf19fc0fff0703311 0x97f19fc0fff07033

def z891 : W := mkw 0xa82db6d800000000 0x04a82db6d8000000 0xf9fffff80000003f 0xe6f9fffff8000000

def z892 : W := mkw 0x12edb6d800000000 0x0412edb6d8000000 0x00fffff80000003c 0x0600fffff8000000

def z893 : W := mkw 0xa81b2006c8030088 0x00a81b2006c80300 0xf81ff807fc03c0dd 0xf7f81ff807fc03c0

def z894 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e3c0cc 0xe5c71e07e783e3c0

def z895 : W := mkw 0xa80b6802dc01b08e 0x02a80b6802dc01b0 0xf00ff803f001f098 0x47f00ff803f001f0

def z896 : W := mkw 0x0032186c84271509 0x400032186c842715 0xc9fe38ff8c7e3f77 0xbdc9fe38ff8c7e3f

def z897 : W := mkw 0xa81b6826dc27b58f 0x42a81b6826dc27b5 0xf89ff81ffc7fffff 0xfff89ff81ffc7fff

def z898 : W := mkw 0x0020104800000000 0x0000201048000000 0x09f038fc0c7e3f77 0xb809f038fc0c7e3f

def z899 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3681c7187393ff3f 0x1a3681c7187393ff

def z900 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf89ff81ffc03f0ff 0xf7f89ff81ffc03f0

def z901 : W := mkw 0xa81b6826dc23b48f 0x02a81b6826dc23b4 0xf91ff8e7fc63f0dd 0xf7f91ff8e7fc63f0

def z902 : W := mkw 0x002db6d800000000 0x04002db6d8000000 0x097ffff80000003c 0x86097ffff8000000

def z903 : W := mkw 0xffddaeb404261501 0x44ffddaeb4042615 0xf60fc7040c7e3f48 0x5ef60fc7040c7e3f

def z904 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffff80000002a 0xc6fffffff8000000

def z905 : W := mkw 0x002db6d800000000 0x04002db6d8000000 0x011ffff80000003e 0xa6011ffff8000000

def z906 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf9fff81ffc7fffff 0xfff9fff81ffc7fff

def z907 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xff600007ffec00c2 0xe9ff600007ffec00

def z908 : W := mkw 0x57e497d923d84a70 0x8c57e497d923d84a 0x07e007f803fc0f22 0x0807e007f803fc0f

def z909 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc79e07ff83e3ccff 0xedc79e07ff83e3cc

def z910 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfe1ffff80000003d 0xe6fe1ffff8000000

def z911 : W := mkw 0x45160da586e75d49 0x4145160da586e75d 0xc79e07ff8fffffff 0xfdc79e07ff8fffff

def z912 : W := mkw 0xbac000036b5800f0 0x08bac000036b5800 0xf8e00007fffc00c1 0xf9f8e00007fffc00

def z913 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xffe0001ffffc33d3 0xf9ffe0001ffffc33

def z914 : W := mkw 0xffcda6936b5800f0 0x0cffcda6936b5800 0xffefc71ffffc00ff 0xffffefc71ffffc00

def z915 : W := mkw 0xffedb6d902400040 0x04ffedb6d9024000 0xffffffff8ffc00ff 0xffffffffff8ffc00

def z916 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc7fe07e783ffccee 0xedc7fe07e783ffcc

def z917 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf01ff803f003f0dd 0x77f01ff803f003f0

def z918 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xffe1c007fffc00df 0xfbffe1c007fffc00

def z919 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xfe1ff807ff83f0df 0xfffe1ff807ff83f0

def z920 : W := mkw 0x0030186c04261501 0x400030186c042615 0xc9f038ff8c7e3ff7 0xf9c9f038ff8c7e3f

def z921 : W := mkw 0xed6db6d800000000 0x04ed6db6d8000000 0xc01ffff80000003c 0x06c01ffff8000000

def z922 : W := mkw 0x0030186c04261501 0x400030186c042615 0x39f038fc7c7e3ff7 0xf839f038fc7c7e3f

def z923 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xfffffffbf39000ff 0xfffffffffbf39000

def z924 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xfffffffffffe3fff 0xfffffffffffffe3f

def z925 : W := mkw 0xa82db6d800000000 0x04a82db6d8000000 0x381ffff80000003d 0x06381ffff8000000

def z926 : W := mkw 0xffedb6d902400040 0x04ffedb6d9024000 0xfffffffb838000bf 0xe7fffffffb838000

def z927 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xff600007fffc00c0 0xd9ff600007fffc00

def z928 : W := mkw 0xbaa9b25800000000 0x00baa9b258000000 0xfffffff80000003f 0xe6fffffff8000000

def z929 : W := mkw 0xa81b6826dc27b58f 0x42a81b6826dc27b5 0xf81ff807fc6ff0dd 0xf7f81ff807fc6ff0

def z930 : W := mkw 0x0030186c04261501 0x400030186c042615 0x0ff038fc0ffe3ff7 0xf80ff038fc0ffe3f

def z931 : W := mkw 0xed124927dee3fccf 0x03ed124927dee3fc 0xff000007ffe3fcc3 0xf9ff000007ffe3fc

def z932 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffff8007c003f 0xeefffffff8007c00

def z933 : W := mkw 0x0030186c04261501 0x400030186c042615 0xc9fe38fc0c7e3f7f 0xfcc9fe38fc0c7e3f

def z934 : W := mkw 0xbaedb6da691800b0 0x0cbaedb6da691800 0x38fffff87c1c003d 0x1638fffff87c1c00

def z935 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xfffffffbff9c00bf 0xf7fffffffbff9c00

def z936 : W := mkw 0x452db6d800000000 0x04452db6d8000000 0xc61ffff80000003c 0x46c61ffff8000000

def z937 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfefffff80000003d 0x46fefffff8000000

def z938 : W := mkw 0x002db6d800000000 0x04002db6d8000000 0x09fffffc0c7c007f 0xbe09fffffc0c7c00

def z939 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf97ff807fc6ff0dd 0xf7f97ff807fc6ff0

def z940 : W := mkw 0xffcda6936b5800f0 0x0cffcda6936b5800 0xffffff07fffc00df 0xffffffff07fffc00

def z941 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xff7fffe7ffec0088 0xc7ff7fffe7ffec00

def z942 : W := mkw 0x4516058480834808 0x0045160584808348 0xc71e07e78383ccee 0xedc71e07e78383cc

def z943 : W := mkw 0x4506058182c14848 0x014506058182c148 0xc70e07e38381c0aa 0x45c70e07e38381c0

def z944 : W := mkw 0xed4000036b5800f0 0x08ed4000036b5800 0xc9600007ffec0080 0x81c9600007ffec00

def z945 : W := mkw 0xed6db6db4a4800d0 0x0ced6db6db4a4800 0xc97fffff8c6c003c 0x87c97fffff8c6c00

def z946 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3681c7187383ffbf 0x623681c7187383ff

def z947 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e3ccc8 0xcdc71e07e783e3cc

def z948 : W := mkw 0x45160da586e35c49 0x0145160da586e35c 0xcf9e3fff8ff3ffff 0xfdcf9e3fff8ff3ff

def z949 : W := mkw 0xffedb6d821180030 0x0cffedb6d8211800 0xfffffff8001c003f 0xe6fffffff8001c00

def z950 : W := mkw 0xa80b6002d801a08e 0x02a80b6002d801a0 0xf81ff803f003f0dd 0xf7f81ff803f003f0

def z951 : W := mkw 0xa81b6826dc27b58f 0x42a81b6826dc27b5 0xf91ff8e7fc7fffff 0xfff91ff8e7fc7fff

def z952 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3781c71c73f3ffff 0xfa3781c71c73f3ff

def z953 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3681c7187393ffbe 0x4a3681c7187393ff

def z954 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xcffe07e783e3ccef 0xedcffe07e783e3cc

def z955 : W := mkw 0xffedb6d923500060 0x04ffedb6d9235000 0xfffffffff3f000ff 0xfffffffffff3f000

def z956 : W := mkw 0xffedb6da48080090 0x0cffedb6da480800 0xfffffff80c0c003f 0xe6fffffff80c0c00

def z957 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf91ff8e7fc03f0ff 0xf7f91ff8e7fc03f0

def z958 : W := mkw 0xa80d248000000000 0x00a80d2480000000 0xf81fffe00000003d 0xe6f81fffe0000000

def z959 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xf71ffff80000003e 0xe6f71ffff8000000

def z960 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf9fff807fc03f0df 0xf7f9fff807fc03f0

def z961 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffff800000033 0x86fffffff8000000

def z962 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0x3ffffff80000003f 0x063ffffff8000000

def z963 : W := mkw 0xbaedb6d800000000 0x04baedb6d8000000 0x301ffff80000003c 0x06301ffff8000000

def z964 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xf9fffff80000003d 0x86f9fffff8000000

def z965 : W := mkw 0xffedb6db4a4000c0 0x04ffedb6db4a4000 0xffffffffffe000ff 0xffffffffffffe000

def z966 : W := mkw 0xed2db6d800000000 0x04ed2db6d8000000 0xff1ffff80000003f 0xe6ff1ffff8000000

def z967 : W := mkw 0xa82db6d800000000 0x04a82db6d8000000 0xf01ffff80000003c 0x46f01ffff8000000

def z968 : W := mkw 0xed6db6d800000000 0x04ed6db6d8000000 0xf97ffff80000003d 0xe6f97ffff8000000

def z969 : W := mkw 0x57c000036b5800f0 0x0857c000036b5800 0x37e00007fffc00c3 0x7937e00007fffc00

def z970 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xffe00007fffe0ce7 0xf9ffe00007fffe0c

def z971 : W := mkw 0x57edb6d800000000 0x0457edb6d8000000 0x061ffff80000003c 0x06061ffff8000000

def z972 : W := mkw 0x0020186804241501 0x4000201868042415 0x09e038f80c7e3f77 0x3809e038f80c7e3f

def z973 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xff600007ffec00c1 0xf1ff600007ffec00

def z974 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffff800100f3f 0xeefffffff800100f

def z975 : W := mkw 0xa86db6d800000000 0x04a86db6d8000000 0x087ffff80000003c 0x06087ffff8000000

def z976 : W := mkw 0x454000036b5800f0 0x08454000036b5800 0x01600007fffc00c0 0x1901600007fffc00

def z977 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xff7fffe00000002e 0xe6ff7fffe0000000

def z978 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xffe00007ffec0083 0xe1ffe00007ffec00

def z979 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf81ff807fc03fcff 0xfff81ff807fc03fc

def z980 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e1ccaa 0xcdc71e07e783e1cc

def z981 : W := mkw 0x4506058182c14848 0x014506058182c148 0xc71e07e38383ccee 0xedc71e07e38383cc

def z982 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffffc0060007f 0xeefffffffc006000

def z983 : W := mkw 0xa80b6802dc01b08e 0x02a80b6802dc01b0 0xf80ff807fc01f0d9 0xf7f80ff807fc01f0

def z984 : W := mkw 0x57edb6d923580070 0x0c57edb6d9235800 0x07fffff803fc003e 0x0e07fffff803fc00

def z985 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xffffffffff8000ff 0xf7ffffffffff8000

def z986 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf8fff807fc1ff0dd 0xf7f8fff807fc1ff0

def z987 : W := mkw 0xa80b6802dc01b08e 0x02a80b6802dc01b0 0xf80ff803fc01c088 0x47f80ff803fc01c0

def z988 : W := mkw 0x450605a182e14c49 0x01450605a182e14c 0xc70e07e383e1c088 0x45c70e07e383e1c0

def z989 : W := mkw 0x12adb6d800000000 0x0412adb6d8000000 0x3ffffff80000003f 0xe63ffffff8000000

def z990 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e1c0ca 0xedc71e07e783e1c0

def z991 : W := mkw 0xffedb6da691800b0 0x0cffedb6da691800 0xfffffffc7c7c007f 0xfefffffffc7c7c00

def z992 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3e81c71c7f93ffff 0xfa3e81c71c7f93ff

def z993 : W := mkw 0xffc920036b5800f0 0x08ffc920036b5800 0xffe1f807fffc00d3 0xfbffe1f807fffc00

def z994 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xfee00007fffc00c1 0x59fee00007fffc00

def z995 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x37e1c71873ffffff 0x7a37e1c71873ffff

def z996 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e3cc2e 0x8dc71e07e783e3cc

def z997 : W := mkw 0xffc404836b5800f0 0x08ffc404836b5800 0xffe007e7fffc00e3 0xf9ffe007e7fffc00

def z998 : W := mkw 0xffc404836b5800f0 0x08ffc404836b5800 0xffee0707fffc00cb 0xfdffee0707fffc00

def z999 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xffffffe00000000b 0xe6ffffffe0000000

def z1000 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xf7fffff80000003e 0x46f7fffff8000000

def z1001 : W := mkw 0x0030186c04261501 0x400030186c042615 0x09f038f80c7e3f37 0x1809f038f80c7e3f

def z1002 : W := mkw 0xbaedb6d800000000 0x04baedb6d8000000 0x3efffff80000003f 0x663efffff8000000

def z1003 : W := mkw 0x0030186c04261501 0x400030186c042615 0x09e038fc0c7e3f73 0x1809e038fc0c7e3f

def z1004 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xcf7e07e78fefccee 0xedcf7e07e78fefcc

def z1005 : W := mkw 0x45160da586e75d49 0x4145160da586e75d 0xc71e07e78fefccee 0xedc71e07e78fefcc

def z1006 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xfff000e7fffc00e7 0xf9fff000e7fffc00

def z1007 : W := mkw 0xa85b6806dc0bb09e 0x0aa85b6806dc0bb0 0xf87ff807fc0ff0dd 0xf7f87ff807fc0ff0

def z1008 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc61e07e38381c088 0x45c61e07e38381c0

def z1009 : W := mkw 0x12c0c3103198ea34 0x8812c0c3103198ea 0x36e1c718739fffff 0x7a36e1c718739fff

def z1010 : W := mkw 0xffedb6da691800b0 0x0cffedb6da691800 0xfffffff87000003f 0xe6fffffff8700000

def z1011 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf81ff803fc03f09d 0x57f81ff803fc03f0

def z1012 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xfffe0007fffc00cf 0xfdfffe0007fffc00

def z1013 : W := mkw 0x0000c3101080ea04 0x800000c3101080ea 0x3601c7187383ffff 0x7a3601c7187383ff

def z1014 : W := mkw 0x00124925b7f7ff6d 0xc100124925b7f7ff 0x00000007ffffffc0 0x1900000007ffffff

def z1015 : W := mkw 0xff8da69000000000 0x00ff8da690000000 0xff9ffff80000003f 0xe6ff9ffff8000000

def z1016 : W := mkw 0xed6db6d800000000 0x04ed6db6d8000000 0xcf7ffff80000003e 0xe6cf7ffff8000000

def z1017 : W := mkw 0x0030186c04261501 0x400030186c042615 0x09f038fc0c7e3f62 0x9809f038fc0c7e3f

def z1018 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e383e3ccae 0x4dc71e07e383e3cc

def z1019 : W := mkw 0x45160da586e35c49 0x0145160da586e35c 0xcffe3fe78ffffcff 0xfdcffe3fe78ffffc

def z1020 : W := mkw 0x002db6d800000000 0x04002db6d8000000 0x001ffff800023f3c 0x06001ffff800023f

def z1021 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf81ff803f003f09d 0xe7f81ff803f003f0

def z1022 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffff80010007f 0xfefffffff8001000

def z1023 : W := mkw 0x002db6d800000000 0x04002db6d8000000 0x301ffff80000003d 0x66301ffff8000000

def z1024 : W := mkw 0x00124927fffbfcff 0x0b00124927fffbfc 0x00000007fffffcc0 0x1900000007fffffc

def z1025 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e1c0ae 0xe5c71e07e783e1c0

def z1026 : W := mkw 0x003bfb7c94a7ff0f 0xc2003bfb7c94a7ff 0x001ffff80003ff3c 0x06001ffff80003ff

def z1027 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3ee1c7187f9fffff 0x7a3ee1c7187f9fff

def z1028 : W := mkw 0x002db6d800000000 0x04002db6d8000000 0x061ffff80000003e 0x66061ffff8000000

def z1029 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffffc0c7e3f7f 0xfefffffffc0c7e3f

def z1030 : W := mkw 0x0012492494a3fc0f 0x030012492494a3fc 0x000000000003fc00 0x00000000000003fc

def z1031 : W := mkw 0x45160da586e75d49 0x4145160da586e75d 0xcf1e3fe78fffffff 0xfdcf1e3fe78fffff

def z1032 : W := mkw 0x57edb6d800000000 0x0457edb6d8000000 0x37fffff80000003f 0x6637fffff8000000

def z1033 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783f3ffee 0xfdc71e07e783f3ff

def z1034 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf81ff807fc03c0cc 0xe7f81ff807fc03c0

def z1035 : W := mkw 0xffedb6d800040100 0x44ffedb6d8000401 0xfffffff8001c033f 0xe6fffffff8001c03

def z1036 : W := mkw 0x456db6d800000000 0x04456db6d8000000 0x017ffff80000003c 0x06017ffff8000000

def z1037 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf81ff807fc03f09c 0xc7f81ff807fc03f0

def z1038 : W := mkw 0xa80b6802dc01b08e 0x02a80b6802dc01b0 0xf81ff803fc01f09d 0xf7f81ff803fc01f0

def z1039 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3601c7187383fffd 0x723601c7187383ff

def z1040 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf01ff807fc03f0dc 0x57f01ff807fc03f0

def z1041 : W := mkw 0x450605a182e14c49 0x01450605a182e14c 0xc71e07e383e1ccae 0xedc71e07e383e1cc

def z1042 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc61e07e78383ccec 0xe5c61e07e78383cc

def z1043 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3601c7187393fffc 0x5a3601c7187393ff

def z1044 : W := mkw 0x00124926dca3fc8f 0x0300124926dca3fc 0x00000007fc03fcc0 0x1100000007fc03fc

def z1045 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffff800023f3f 0xe6fffffff800023f

def z1046 : W := mkw 0x0030186c04261501 0x400030186c042615 0x39f1f8fc0c7e3f7f 0xfa39f1f8fc0c7e3f

def z1047 : W := mkw 0x000041001080e804 0x00000041001080e8 0x3681c7187393ffff 0x7a3681c7187393ff

def z1048 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xffe00007fffc0082 0xc9ffe00007fffc00

def z1049 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf01ff807f003f0dc 0xe7f01ff807f003f0

def z1050 : W := mkw 0xffedb6db4a4800d0 0x0cffedb6db4a4800 0xffffffff8c7c007f 0xffffffffff8c7c00

def z1051 : W := mkw 0x45160da586e35c49 0x0145160da586e35c 0xcf1e3fe78fe3ccee 0xedcf1e3fe78fe3cc

def z1052 : W := mkw 0x000000036b5800f0 0x08000000036b5800 0x08e00007fffc00c1 0x1908e00007fffc00

def z1053 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xf71e07e7f3e3ccef 0xfdf71e07e7f3e3cc

def z1054 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc79e07e783f3ccef 0xfdc79e07e783f3cc

def z1055 : W := mkw 0xffedb6d821100020 0x04ffedb6d8211000 0xfffffff80390003f 0xeefffffff8039000

def z1056 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf80ff807fc03f0d9 0x57f80ff807fc03f0

def z1057 : W := mkw 0xa82db6d800000000 0x04a82db6d8000000 0xc81ffff80000003c 0x86c81ffff8000000

def z1058 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3601c7187383fffe 0x6a3601c7187383ff

def z1059 : W := mkw 0xed4000034a4800d0 0x08ed4000034a4800 0xff600007ffec00c3 0xf9ff600007ffec00

def z1060 : W := mkw 0xba800002691000a0 0x00ba800002691000 0xffe00007fffc00c3 0xf9ffe00007fffc00

def z1061 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e38383ccae 0xe5c71e07e38383cc

def z1062 : W := mkw 0xed4000036b5800f0 0x08ed4000036b5800 0xc9e00007fffc00c3 0xb9c9e00007fffc00

def z1063 : W := mkw 0x002db6d800000000 0x04002db6d8000000 0x08fffff80000003d 0x0608fffff8000000

def z1064 : W := mkw 0xffc082136b5800f0 0x08ffc082136b5800 0xffe1c707fffc00cb 0xfbffe1c707fffc00

def z1065 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffffc0c00007f 0xf6fffffffc0c0000

def z1066 : W := mkw 0xa80000036b5800f0 0x08a80000036b5800 0xf9e00007fffc00c3 0xf9f9e00007fffc00

def z1067 : W := mkw 0xed6d34c800000000 0x04ed6d34c8000000 0xff7fffe00000003f 0xe6ff7fffe0000000

def z1068 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0xf69fc7187393ffff 0xfef69fc7187393ff

def z1069 : W := mkw 0x450000036b5800f0 0x08450000036b5800 0xcfe00007fffc00c3 0xf9cfe00007fffc00

def z1070 : W := mkw 0xffc920036b5800f0 0x08ffc920036b5800 0xfffe3807fffc00c3 0xfdfffe3807fffc00

def z1071 : W := mkw 0x0030186c04261501 0x400030186c042615 0x09f038fc0c7e3f36 0x8809f038fc0c7e3f

def z1072 : W := mkw 0xbaadb6d800000000 0x04baadb6d8000000 0xfe9ffff80000003f 0xe6fe9ffff8000000

def z1073 : W := mkw 0xa81b6826dc23b48f 0x02a81b6826dc23b4 0xf81ff8e7fc03fcfd 0xf7f81ff8e7fc03fc

def z1074 : W := mkw 0xffc486936b5800f0 0x0cffc486936b5800 0xffe00707fffc00c3 0xf9ffe00707fffc00

def z1075 : W := mkw 0xbaedb6d800000000 0x04baedb6d8000000 0xf8fffff80000003d 0xe6f8fffff8000000

def z1076 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc61e07e783e3ccec 0x4dc61e07e783e3cc

def z1077 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3681c7187393ffd9 0x5a3681c7187393ff

def z1078 : W := mkw 0x00124927dee7fdcf 0x4300124927dee7fd 0x00000007ffffffc0 0x1900000007ffffff

def z1079 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf81ff807fc03f01d 0x97f81ff807fc03f0

def z1080 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3791c7f87393ffff 0xfa3791c7f87393ff

def z1081 : W := mkw 0xa84000036b5800f0 0x08a84000036b5800 0x08600007fffc00c0 0x1908600007fffc00

def z1082 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xffe00007fffe3fc3 0xf9ffe00007fffe3f

def z1083 : W := mkw 0x45160da586e35c49 0x0145160da586e35c 0xc71e3fe783e3fcfe 0xedc71e3fe783e3fc

def z1084 : W := mkw 0x000d248000000000 0x00000d2480000000 0x001fffe00000003c 0x06001fffe0000000

def z1085 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffffc0c6c003f 0xe6fffffffc0c6c00

def z1086 : W := mkw 0x450d248000000000 0x00450d2480000000 0xc71fffe00000003e 0xe6c71fffe0000000

def z1087 : W := mkw 0xed3f3cefce6715cb 0x43ed3f3cefce6715 0xc97e38e78c6c0000 0x85c97e38e78c6c00

def z1088 : W := mkw 0xed6db6d800000000 0x04ed6db6d8000000 0xc97fffe000000008 0x86c97fffe0000000

def z1089 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e78fffccee 0xfdc71e07e78fffcc

def z1090 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xfe1fff07fc03f0ff 0xf7fe1fff07fc03f0

def z1091 : W := mkw 0x002db6d800000000 0x04002db6d8000000 0x009ffff800123f7f 0x3e009ffff800123f

def z1092 : W := mkw 0x57a496d800000000 0x0057a496d8000000 0xfffffff80000003f 0xe6fffffff8000000

def z1093 : W := mkw 0xffedb6d923580070 0x0cffedb6d9235800 0xfffffffc0ffc007f 0xfefffffffc0ffc00

def z1094 : W := mkw 0xffedb6d800000000 0x04ffedb6d8000000 0xfffffff8038000ff 0xeefffffff8038000

def z1095 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xffe00007fffc0081 0xd1ffe00007fffc00

def z1096 : W := mkw 0x00124927fff3feef 0x8300124927fff3fe 0x00000007fff3ffc0 0x1900000007fff3ff

def z1097 : W := mkw 0x4506058182c14848 0x014506058182c148 0xc71e07e38381c088 0xc5c71e07e38381c0

def z1098 : W := mkw 0xffcd248000000000 0x00ffcd2480000000 0xffffffe00000003f 0xe6ffffffe0000000

def z1099 : W := mkw 0x57a497f923f44f61 0xc157a497f923f44f 0x07e007f803fc0f22 0x0807e007f803fc0f

def z1100 : W := mkw 0xbac000036b5800f0 0x08bac000036b5800 0x39e00007fffc00c3 0xb939e00007fffc00

def z1101 : W := mkw 0x0030186c04261501 0x400030186c042615 0x09f038fc0c7e3f51 0x9809f038fc0c7e3f

def z1102 : W := mkw 0xffc000036b5800f0 0x08ffc000036b5800 0xffe0001ffffc0fe3 0xf9ffe0001ffffc0f

def z1103 : W := mkw 0x12adb6d800000000 0x0412adb6d8000000 0x361ffff80000003c 0x46361ffff8000000

def z1104 : W := mkw 0xffedb6da691800b0 0x0cffedb6da691800 0xfffffff87f9c00ff 0xfefffffff87f9c00

def z1105 : W := mkw 0x1280c3103190ea24 0x801280c3103190ea 0x3681c7187393fff3 0x1a3681c7187393ff

def z1106 : W := mkw 0xa81b60049003a00c 0x00a81b60049003a0 0xf81ff807f003f0dd 0xf7f81ff807f003f0

def z1107 : W := mkw 0xffedb6d902480050 0x0cffedb6d9024800 0xfffffff8006c003f 0xe6fffffff8006c00

def z1108 : W := mkw 0xa81b6806dc03b08e 0x02a81b6806dc03b0 0xf89ff81ffc13f3dd 0xf7f89ff81ffc13f3

def z1109 : W := mkw 0x0030186c04261501 0x400030186c042615 0x09f038fc0c7c3f33 0x9809f038fc0c7c3f

def z1110 : W := mkw 0x000000036b5800f0 0x08000000036b5800 0x01e00007fffc00c2 0x1901e00007fffc00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z7,z4,z6,z8]),(0,[z0,z1,z9,z2,z3,z10,z6]),(0,[z11,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z13,z4,z6]),(0,[z14,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z15,z3,z4,z6]),(0,[z0,z1,z2,z16,z3,z4,z6]),(0,[z0,z1,z2,z3,z17,z4,z6])],[(0,[z18,z0,z1,z2,z3,z4,z6]),(0,[z19,z0,z1,z2,z3,z4,z20]),(0,[z21,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z22,z3,z10,z4]),(0,[z0,z1,z2,z3,z23,z4,z6]),(0,[z0,z1,z24,z2,z3,z4,z6])],[(0,[z25,z0,z26,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z27,z4,z6]),(0,[z0,z28,z1,z2,z3,z4,z6]),(0,[z29,z0,z1,z2,z3,z4,z30]),(0,[z0,z1,z2,z31,z3,z4,z6]),(0,[z0,z32,z1,z2,z33,z4,z6]),(0,[z0,z1,z34,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z35,z6])],[(0,[z29,z36,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z37,z6]),(0,[z19,z0,z1,z2,z3,z4,z38]),(0,[z0,z1,z2,z3,z4,z39,z6])],[(0,[z0,z1,z2,z3,z40,z4,z6]),(0,[z0,z41,z1,z42,z3,z4,z6]),(0,[z0,z1,z2,z3,z43,z4,z30]),(0,[z44,z0,z1,z2,z3,z4,z6]),(0,[z45,z0,z1,z2,z3,z4,z6])],[(0,[z46,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z47,z3,z4,z6]),(0,[z48,z0,z2,z3,z7,z4,z6]),(0,[z0,z1,z2,z3,z49,z4,z6]),(0,[z0,z1,z50,z2,z3,z4,z51]),(0,[z0,z1,z2,z3,z4,z52,z6]),(0,[z0,z53,z1,z2,z3,z4,z6])],[(0,[z0,z41,z42,z2,z3,z4,z6]),(0,[z0,z54,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z55,z6])]],
   [[(1,[z0,z1,z2,z56,z4,z6]),(0,[z0,z1,z50,z2,z57,z3,z4])],[(0,[z0,z1,z2,z3,z4,z58,z6]),(0,[z0,z1,z59,z2,z3,z4,z6])],[(0,[z0,z1,z60,z2,z3,z4,z6]),(0,[z61,z0,z1,z62,z3,z4,z6]),(0,[z0,z1,z2,z3,z63,z4,z6]),(0,[z36,z0,z1,z9,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z64,z6]),(1,[z0,z1,z2,z3,z65,z30])],[(0,[z0,z66,z1,z2,z3,z4,z6]),(0,[z67,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z68]),(0,[z69,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z70,z6]),(0,[z0,z1,z71,z2,z3,z4,z6]),(0,[z72,z73,z1,z2,z3,z4,z6]),(0,[z74,z0,z1,z3,z75,z4,z6]),(0,[z0,z1,z2,z3,z76,z4,z6])],[(0,[z77,z0,z1,z2,z78,z4,z6]),(0,[z79,z0,z1,z2,z3,z4,z6]),(0,[z80,z0,z1,z2,z3,z4,z30]),(0,[z0,z1,z2,z57,z3,z81,z6]),(0,[z82,z36,z0,z1,z2,z3,z4])],[(0,[z83,z0,z1,z2,z3,z4,z6]),(0,[z84,z0,z1,z2,z3,z4,z20]),(0,[z84,z36,z0,z1,z2,z3,z4]),(0,[z0,z85,z1,z2,z3,z4,z6]),(0,[z86,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z87,z6])],[(0,[z0,z1,z2,z3,z88,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z89]),(0,[z0,z90,z1,z2,z3,z4,z6]),(0,[z91,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z92,z4,z6]),(1,[z0,z1,z2,z57,z4,z93]),(0,[z0,z1,z2,z3,z94,z4,z6]),(0,[z0,z1,z2,z95,z3,z4,z6])]],
   [[(0,[z96,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z97,z6]),(0,[z77,z0,z1,z2,z3,z4,z6]),(0,[z84,z0,z1,z2,z3,z4,z38]),(0,[z98,z36,z0,z1,z2,z3,z4]),(0,[z0,z1,z99,z2,z3,z4,z6]),(0,[z100,z0,z1,z2,z3,z4,z6]),(0,[z101,z0,z1,z2,z3,z4,z30])],[(0,[z0,z1,z2,z3,z4,z6,z102]),(0,[z0,z1,z2,z3,z103,z4,z6]),(0,[z0,z1,z104,z2,z3,z4,z6])],[(1,[z0,z1,z105,z3,z4,z6]),(0,[z72,z1,z2,z3,z4,z6,z106]),(0,[z0,z1,z2,z3,z4,z30,z106]),(0,[z84,z0,z1,z107,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z108])],[(0,[z109,z1,z26,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z110]),(1,[z0,z1,z2,z111,z3,z4]),(0,[z0,z1,z2,z112,z4,z113,z6]),(1,[z0,z1,z2,z114,z3,z30])],[(0,[z0,z1,z115,z116,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z117,z6]),(0,[z61,z0,z2,z62,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z118]),(0,[z0,z1,z2,z119,z3,z4,z6])],[(0,[z0,z1,z2,z3,z120,z4,z6]),(0,[z0,z1,z121,z2,z3,z4,z6]),(0,[z0,z2,z3,z122,z4,z123,z6]),(0,[z124,z0,z1,z2,z3,z4,z6]),(0,[z0,z125,z1,z2,z3,z4,z6]),(0,[z126,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z127,z4,z6])],[(0,[z0,z32,z1,z2,z43,z4,z6]),(0,[z128,z0,z1,z2,z3,z129,z4]),(0,[z0,z1,z2,z3,z4,z130,z6])],[(0,[z131,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z116,z42,z3,z4,z6]),(0,[z0,z132,z1,z2,z3,z4,z6])]],
   [[(0,[z133,z0,z1,z2,z3,z4,z6]),(0,[z72,z0,z1,z2,z3,z4,z134]),(0,[z135,z0,z1,z2,z3,z4,z6]),(0,[z136,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z4,z30]),(0,[z137,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z138,z3,z4,z6]),(0,[z139,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z140,z3,z4,z6]),(0,[z0,z141,z1,z2,z3,z122,z6]),(0,[z36,z0,z141,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z142,z4,z6])],[(0,[z0,z1,z2,z3,z10,z6,z30]),(1,[z36,z0,z1,z2,z3,z30])],[(1,[z29,z1,z2,z143,z4,z6]),(0,[z0,z41,z1,z62,z3,z4,z6]),(0,[z0,z1,z2,z33,z3,z4,z30]),(0,[z80,z0,z1,z2,z114,z3,z6])],[(0,[z0,z144,z1,z2,z3,z4,z6]),(0,[z145,z0,z1,z2,z3,z4,z6]),(0,[z146,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z33,z3,z43,z4,z6]),(0,[z0,z1,z2,z3,z4,z147,z6]),(0,[z36,z0,z1,z50,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z148,z6]),(0,[z149,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z150]),(0,[z151,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z152,z3,z4,z6]),(0,[z153,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z154,z6]),(0,[z36,z0,z1,z155,z2,z3,z4]),(0,[z0,z156,z1,z2,z3,z4,z6])],[(0,[z0,z1,z115,z157,z3,z4,z6]),(0,[z36,z0,z1,z2,z3,z4,z106]),(0,[z0,z1,z2,z158,z3,z4,z6]),(0,[z0,z1,z2,z159,z3,z4,z6]),(0,[z0,z160,z1,z2,z3,z161,z6]),(0,[z0,z1,z2,z3,z113,z6,z30])],[(0,[z0,z1,z2,z3,z162,z4,z6]),(0,[z0,z1,z2,z3,z4,z163,z6]),(0,[z36,z0,z1,z2,z3,z65,z4])]],
   [[(0,[z0,z164,z1,z2,z3,z4,z6]),(0,[z165,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z122,z4,z30]),(0,[z128,z36,z0,z1,z2,z3,z4]),(0,[z166,z36,z0,z1,z2,z3,z4])],[(0,[z0,z109,z2,z3,z4,z123,z6]),(0,[z167,z0,z1,z2,z3,z4,z6]),(0,[z168,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z57,z78,z4,z6]),(0,[z169,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z129,z4,z6]),(0,[z170,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z78,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z171,z6]),(0,[z172,z0,z1,z2,z3,z4,z6]),(0,[z173,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z174,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z175,z4,z6]),(0,[z0,z1,z2,z176,z3,z4,z6]),(0,[z44,z0,z1,z2,z3,z10,z6]),(0,[z0,z177,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z30,z30])],[(0,[z36,z25,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z20]),(0,[z36,z0,z1,z2,z3,z127,z4])],[(0,[z178,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z179,z2,z3,z4,z6]),(0,[z0,z1,z2,z57,z3,z4,z6])],[(0,[z0,z1,z2,z3,z180,z4,z6]),(0,[z0,z1,z2,z157,z3,z4,z6]),(0,[z72,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z181,z4,z6]),(0,[z0,z182,z1,z2,z3,z4,z6]),(1,[z183,z0,z1,z2,z3,z4]),(0,[z128,z0,z1,z2,z3,z4,z51])],[(0,[z0,z1,z184,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z185,z6]),(0,[z0,z1,z2,z3,z186,z4,z6]),(1,[z0,z1,z2,z3,z161,z6]),(0,[z0,z1,z9,z2,z3,z4,z6])],[(0,[z0,z1,z2,z187,z3,z4,z6]),(0,[z0,z1,z2,z3,z188,z4,z6]),(0,[z0,z189,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z190,z6]),(0,[z0,z1,z2,z3,z4,z191,z6]),(1,[z0,z1,z2,z3,z10,z30]),(0,[z0,z192,z1,z2,z3,z4,z6]),(0,[z128,z0,z1,z2,z57,z3,z4])]],
   [[(0,[z0,z1,z2,z193,z3,z4,z6]),(0,[z0,z1,z2,z3,z194,z4,z6]),(0,[z0,z1,z2,z3,z195,z4,z6]),(0,[z196,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z51]),(0,[z0,z1,z2,z197,z3,z4,z6]),(0,[z36,z0,z1,z2,z114,z3,z4])],[(0,[z198,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z199,z4,z6]),(0,[z200,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z3,z4,z6]),(1,[z0,z1,z2,z3,z201,z6]),(0,[z0,z1,z115,z2,z3,z4,z30]),(0,[z0,z1,z2,z202,z3,z4,z6]),(0,[z0,z1,z2,z203,z3,z4,z6]),(0,[z0,z1,z2,z204,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z205,z6]),(0,[z206,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z30,z207])],[(0,[z0,z1,z2,z3,z4,z208,z6]),(0,[z0,z1,z2,z3,z209,z4,z6]),(0,[z0,z1,z2,z3,z210,z4,z6]),(1,[z0,z1,z2,z3,z122,z30])],[(1,[z0,z1,z211,z3,z4,z6]),(0,[z212,z0,z1,z211,z3,z4,z6]),(0,[z48,z0,z1,z2,z3,z4,z30])],[(0,[z0,z1,z2,z213,z3,z4,z6]),(0,[z0,z1,z2,z3,z214,z4,z6]),(0,[z48,z36,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z215]),(0,[z0,z216,z1,z2,z3,z4,z6]),(0,[z36,z0,z1,z2,z3,z4,z30])],[(0,[z73,z1,z2,z3,z117,z4,z6]),(0,[z0,z1,z2,z3,z217,z4,z6]),(0,[z36,z36,z0,z1,z2,z3,z4])]],
   [[(0,[z218,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z219]),(0,[z220,z0,z1,z2,z3,z4,z6]),(0,[z0,z221,z1,z2,z3,z4,z6]),(0,[z0,z1,z155,z2,z3,z4,z6])],[(0,[z72,z0,z1,z222,z3,z4,z6]),(0,[z165,z0,z1,z2,z33,z4,z6]),(0,[z36,z0,z32,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z223,z6]),(1,[z0,z1,z2,z3,z49,z4])],[(1,[z0,z1,z2,z224,z4,z6]),(0,[z225,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z226,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z227,z6]),(0,[z36,z0,z1,z2,z3,z43,z4])],[(0,[z0,z1,z2,z78,z33,z4,z6]),(0,[z0,z1,z2,z3,z228,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z8]),(0,[z0,z1,z2,z3,z229,z4,z6])],[(0,[z212,z0,z1,z2,z230,z4,z6]),(0,[z231,z0,z1,z2,z3,z4,z6]),(0,[z232,z0,z1,z2,z3,z4,z6]),(0,[z36,z0,z1,z2,z233,z3,z4]),(0,[z234,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z5,z6]),(0,[z212,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z235,z3,z4,z6]),(0,[z74,z0,z1,z115,z3,z4,z6])],[(0,[z0,z1,z236,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z237,z6]),(0,[z74,z36,z0,z1,z2,z3,z4]),(0,[z36,z0,z1,z2,z57,z3,z4]),(0,[z36,z0,z1,z2,z3,z4,z93])],[(0,[z238,z0,z1,z2,z3,z4,z6]),(0,[z0,z239,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z240,z4,z6]),(1,[z0,z1,z2,z3,z175,z4]),(1,[z0,z1,z2,z3,z4,z241])]],
   [[(0,[z0,z1,z2,z3,z242,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z243]),(0,[z0,z1,z2,z3,z4,z244,z6]),(0,[z0,z1,z2,z3,z245,z4,z6]),(0,[z0,z1,z2,z111,z3,z4,z6]),(0,[z0,z1,z2,z3,z246,z4,z6]),(0,[z36,z0,z247,z1,z2,z3,z4])],[(0,[z98,z0,z109,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z143,z4,z30]),(0,[z248,z0,z1,z2,z3,z4,z6]),(0,[z249,z0,z1,z2,z3,z4,z6]),(0,[z250,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z251,z3,z4,z6]),(0,[z25,z0,z1,z2,z3,z4,z30]),(0,[z0,z1,z116,z3,z4,z58,z6]),(0,[z252,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z253,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z254]),(0,[z1,z116,z2,z157,z3,z4,z6]),(0,[z255,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z8,z20]),(1,[z0,z1,z256,z3,z4,z6]),(0,[z0,z257,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z258]),(0,[z0,z1,z2,z22,z3,z4,z6]),(0,[z36,z0,z1,z2,z3,z10,z4])],[(0,[z72,z0,z1,z2,z259,z4,z6]),(0,[z0,z1,z2,z3,z260,z4,z6])],[(0,[z261,z0,z1,z2,z3,z4,z6]),(0,[z262,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z62,z3,z4,z6])],[(0,[z61,z0,z1,z2,z3,z4,z30]),(0,[z0,z1,z2,z3,z263,z4,z6]),(0,[z0,z1,z264,z2,z3,z4,z6]),(0,[z0,z1,z265,z2,z3,z4,z6])]],
   [[(0,[z266,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z267,z4,z6]),(0,[z36,z0,z1,z2,z3,z117,z4]),(0,[z61,z36,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z268,z4,z6]),(0,[z0,z1,z2,z3,z4,z30,z269])],[(0,[z0,z1,z2,z3,z259,z4,z6]),(0,[z0,z270,z1,z2,z3,z4,z6]),(0,[z36,z0,z1,z2,z3,z122,z4]),(1,[z69,z0,z1,z2,z12,z4])],[(0,[z0,z1,z2,z3,z4,z271,z6]),(0,[z36,z0,z1,z2,z157,z3,z4]),(0,[z0,z1,z2,z33,z143,z4,z6]),(0,[z0,z1,z2,z272,z3,z4,z6]),(0,[z0,z1,z273,z2,z3,z4,z6]),(0,[z0,z1,z274,z2,z3,z4,z6]),(0,[z0,z1,z2,z275,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z276,z6]),(0,[z0,z277,z1,z2,z3,z4,z6])],[(0,[z278,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z78,z75,z4,z6]),(1,[z0,z32,z2,z33,z4,z6]),(0,[z0,z1,z2,z111,z112,z3,z4]),(0,[z0,z1,z2,z279,z3,z4,z6]),(0,[z280,z0,z1,z2,z3,z4,z30]),(0,[z0,z281,z1,z2,z3,z4,z30])],[(0,[z165,z0,z1,z2,z43,z4,z6]),(0,[z0,z1,z2,z282,z3,z4,z6])],[(0,[z0,z1,z2,z283,z3,z4,z6]),(0,[z0,z1,z2,z284,z3,z4,z6]),(0,[z36,z0,z1,z42,z2,z3,z4]),(0,[z0,z160,z1,z2,z3,z4,z30]),(0,[z0,z1,z2,z3,z285,z4,z6]),(0,[z286,z0,z1,z2,z3,z4,z30])],[(0,[z0,z1,z287,z2,z3,z4,z6]),(0,[z0,z1,z2,z78,z43,z4,z6]),(1,[z0,z1,z2,z3,z4,z288]),(0,[z0,z1,z2,z3,z4,z6,z289]),(1,[z0,z1,z2,z3,z290,z4]),(0,[z291,z0,z1,z2,z3,z4,z6])],[(0,[z212,z0,z1,z2,z3,z180,z6]),(0,[z292,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z42,z157,z3,z4,z6]),(0,[z0,z1,z105,z2,z3,z4,z6]),(0,[z0,z1,z2,z293,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z294]),(0,[z0,z1,z2,z3,z4,z295,z30])]],
   [[(0,[z29,z0,z1,z2,z78,z4,z6]),(0,[z296,z0,z1,z2,z3,z4,z6]),(0,[z297,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z50,z2,z3,z4,z6]),(0,[z36,z0,z1,z2,z3,z4,z113])],[(0,[z19,z0,z1,z2,z3,z4,z6]),(0,[z298,z36,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z75,z4,z6]),(0,[z0,z299,z1,z2,z3,z4,z6])],[(0,[z0,z1,z300,z2,z3,z4,z6]),(0,[z301,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z302,z3,z4,z6]),(0,[z0,z1,z2,z3,z303,z4,z6]),(0,[z0,z1,z2,z304,z3,z4,z6]),(1,[z100,z36,z0,z1,z2,z3])],[(0,[z212,z0,z1,z2,z3,z4,z30]),(0,[z0,z109,z1,z2,z3,z4,z30]),(0,[z305,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z143,z75,z4,z6]),(0,[z0,z1,z2,z306,z3,z4,z6]),(0,[z0,z1,z2,z3,z43,z4,z6]),(0,[z0,z1,z2,z3,z4,z307,z6]),(0,[z0,z1,z2,z114,z3,z308,z4]),(0,[z0,z1,z2,z3,z4,z6,z309]),(1,[z0,z1,z2,z3,z4,z30])],[(0,[z212,z36,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z310,z4,z6]),(0,[z0,z1,z2,z3,z4,z311,z6]),(0,[z0,z1,z2,z312,z3,z4,z6])],[(0,[z0,z1,z313,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z143,z43,z4,z6]),(0,[z0,z1,z2,z314,z3,z4,z6]),(0,[z0,z41,z1,z2,z3,z4,z30]),(0,[z0,z1,z2,z3,z4,z315,z6])],[(0,[z0,z26,z2,z3,z4,z123,z6]),(0,[z0,z1,z2,z3,z4,z6,z316]),(0,[z72,z0,z1,z2,z3,z6,z106]),(0,[z84,z0,z1,z2,z181,z4,z6]),(0,[z98,z0,z2,z3,z122,z4,z6]),(0,[z80,z36,z0,z1,z2,z3,z4])],[(0,[z0,z1,z157,z3,z4,z58,z6]),(0,[z80,z0,z1,z2,z78,z4,z6]),(0,[z0,z1,z42,z2,z3,z4,z30]),(0,[z0,z1,z2,z3,z4,z6,z317])],[(0,[z318,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z319,z4,z6]),(0,[z0,z1,z116,z3,z129,z4,z6]),(0,[z0,z1,z2,z3,z320,z4,z6])],[(0,[z321,z0,z1,z2,z3,z4,z6]),(0,[z82,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z117,z4,z6]),(0,[z84,z0,z1,z2,z3,z4,z6]),(0,[z322,z0,z1,z2,z3,z4,z6]),(0,[z323,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z324,z2,z3,z4,z6]),(0,[z0,z1,z2,z233,z3,z4,z30]),(1,[z44,z0,z1,z3,z10,z6])],[(0,[z98,z0,z1,z2,z3,z4,z6])]],
   [[(1,[z0,z1,z251,z3,z4,z6]),(0,[z212,z0,z1,z251,z3,z4,z6]),(0,[z325,z0,z1,z2,z3,z4,z6]),(0,[z326,z0,z1,z2,z3,z4,z6]),(0,[z101,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z327,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z328,z4,z6])],[(0,[z0,z1,z2,z12,z143,z4,z6]),(0,[z0,z1,z2,z3,z38,z201,z6]),(0,[z0,z1,z2,z3,z4,z38,z30]),(0,[z80,z0,z1,z2,z112,z4,z6])],[(0,[z0,z1,z329,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z330]),(0,[z0,z331,z1,z2,z3,z4,z6])],[(0,[z0,z332,z1,z2,z3,z4,z6]),(0,[z333,z0,z1,z2,z3,z4,z6]),(0,[z334,z36,z0,z1,z2,z3,z4])],[(0,[z36,z0,z1,z2,z3,z143,z4]),(0,[z0,z1,z2,z3,z4,z335,z6])],[(0,[z336,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z134]),(0,[z337,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z338,z3,z4,z6]),(0,[z0,z1,z2,z3,z65,z4,z30])],[(0,[z339,z0,z1,z2,z3,z4,z6])],[(0,[z0,z340,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z341,z6]),(0,[z0,z1,z342,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z343,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z344,z6]),(0,[z345,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z346]),(0,[z0,z1,z347,z2,z3,z4,z6]),(0,[z72,z0,z1,z2,z3,z6,z30]),(1,[z84,z1,z2,z3,z4,z38]),(0,[z0,z1,z2,z348,z3,z4,z6])],[(0,[z0,z349,z1,z2,z3,z4,z6]),(0,[z0,z1,z116,z2,z3,z4,z30]),(0,[z350,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z283,z3,z4,z6]),(0,[z0,z1,z351,z2,z3,z4,z6]),(0,[z352,z0,z1,z2,z3,z4,z6]),(0,[z36,z0,z1,z2,z3,z4,z4])],[(0,[z0,z1,z26,z2,z3,z4,z30]),(0,[z0,z1,z2,z353,z3,z4,z6]),(0,[z0,z1,z2,z3,z354,z4,z6]),(0,[z0,z1,z2,z355,z3,z4,z6])],[(0,[z356,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z357]),(0,[z358,z1,z2,z3,z143,z4,z6]),(0,[z0,z1,z2,z3,z4,z359,z6]),(0,[z0,z1,z2,z3,z360,z4,z6]),(0,[z100,z0,z1,z2,z3,z113,z6]),(0,[z0,z1,z2,z361,z57,z3,z6])],[(0,[z0,z1,z2,z3,z362,z4,z6]),(0,[z363,z0,z1,z2,z3,z4,z6]),(0,[z0,z364,z1,z2,z3,z4,z6])],[(0,[z0,z1,z222,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z30,z20])],[(0,[z0,z1,z2,z3,z365,z4,z6]),(0,[z166,z0,z1,z2,z3,z4,z6]),(0,[z366,z0,z1,z2,z3,z4,z6]),(0,[z0,z32,z1,z2,z3,z4,z30]),(0,[z100,z0,z1,z2,z3,z123,z6]),(0,[z36,z0,z160,z1,z2,z3,z4]),(0,[z183,z0,z1,z2,z3,z4,z6]),(0,[z128,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z367,z3,z4,z6]),(0,[z128,z0,z1,z50,z3,z4,z6]),(0,[z0,z1,z2,z368,z3,z4,z6]),(0,[z36,z0,z1,z2,z3,z129,z4]),(0,[z0,z1,z2,z114,z3,z4,z30])],[(0,[z0,z1,z2,z369,z3,z4,z6]),(1,[z61,z0,z62,z3,z4,z6]),(0,[z370,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z371,z4,z6]),(0,[z0,z1,z372,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z373,z0,z1,z2,z3,z4,z6]),(0,[z374,z0,z1,z2,z3,z4,z6]),(0,[z375,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z376,z4,z6]),(0,[z0,z1,z377,z2,z3,z4,z6]),(0,[z44,z0,z1,z2,z3,z58,z6]),(0,[z44,z0,z1,z3,z10,z4,z6]),(0,[z0,z1,z2,z3,z4,z30,z51]),(0,[z0,z1,z2,z3,z378,z4,z6])],[(0,[z0,z379,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z113,z30]),(0,[z380,z0,z1,z2,z3,z4,z6]),(0,[z36,z0,z1,z2,z381,z3,z4])],[(0,[z0,z1,z2,z3,z382,z4,z6]),(0,[z0,z1,z2,z3,z383,z4,z6]),(0,[z0,z1,z2,z3,z4,z30,z93])],[(0,[z384,z0,z1,z2,z3,z4,z6]),(0,[z69,z0,z1,z50,z2,z3,z4])],[(0,[z385,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z116,z62,z3,z4,z6]),(0,[z386,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z387])],[(0,[z29,z1,z2,z3,z143,z4,z6]),(0,[z388,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z389,z4,z6]),(0,[z0,z1,z2,z3,z4,z30,z215])],[(0,[z1,z2,z3,z117,z4,z6,z106]),(0,[z36,z0,z1,z2,z3,z4,z20]),(0,[z0,z1,z2,z3,z390,z4,z6])],[(0,[z0,z1,z2,z3,z4,z391,z6]),(0,[z0,z1,z2,z392,z3,z4,z6]),(0,[z393,z36,z0,z1,z2,z3,z4])],[(0,[z0,z1,z394,z2,z3,z4,z6]),(0,[z29,z77,z1,z2,z3,z4,z6]),(0,[z36,z0,z1,z2,z3,z4,z38]),(0,[z0,z395,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z7,z4,z30]),(0,[z0,z1,z9,z3,z4,z58,z6]),(0,[z396,z0,z1,z2,z3,z4,z6]),(0,[z397,z0,z1,z2,z3,z4,z6]),(0,[z398,z0,z1,z2,z3,z4,z30]),(0,[z399,z36,z0,z1,z2,z3,z4])],[(0,[z48,z0,z1,z2,z3,z4,z6]),(0,[z400,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z308,z4]),(0,[z0,z1,z2,z12,z3,z4,z30]),(0,[z11,z0,z1,z2,z3,z4,z30]),(0,[z36,z0,z1,z2,z401,z3,z4]),(0,[z398,z36,z0,z1,z2,z3,z4])],[(0,[z402,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z403]),(0,[z0,z1,z2,z3,z4,z404,z6]),(0,[z0,z1,z405,z2,z3,z4,z6]),(0,[z100,z0,z1,z2,z3,z58,z6]),(0,[z0,z1,z2,z3,z17,z4,z30])],[(1,[z0,z1,z2,z230,z4,z6]),(0,[z151,z0,z1,z2,z224,z4,z6]),(0,[z36,z0,z1,z2,z3,z4,z51]),(0,[z128,z69,z0,z1,z2,z3,z4])]],
   [[(0,[z0,z1,z2,z107,z3,z4,z6])],[(0,[z77,z358,z1,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z4,z6]),(0,[z406,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z290,z4,z6]),(0,[z407,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z408,z2,z3,z4,z6]),(0,[z0,z1,z2,z409,z3,z4,z30]),(0,[z36,z0,z156,z1,z2,z3,z4])],[(1,[z0,z239,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z410,z4,z6]),(0,[z165,z0,z32,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z411,z4,z6]),(0,[z74,z412,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z413,z3,z4,z6]),(0,[z36,z0,z1,z116,z2,z3,z4]),(0,[z414,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z415,z6]),(0,[z0,z1,z2,z3,z4,z6,z416]),(0,[z0,z1,z2,z3,z4,z417,z6]),(0,[z0,z418,z1,z2,z3,z4,z6])],[(0,[z419,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z116,z3,z75,z4,z6]),(0,[z0,z160,z1,z2,z3,z420,z6]),(0,[z0,z1,z2,z3,z4,z6,z421])],[(0,[z151,z0,z1,z116,z3,z4,z6]),(0,[z0,z1,z2,z233,z143,z4,z6]),(0,[z0,z141,z1,z2,z3,z4,z6]),(0,[z0,z422,z1,z2,z3,z4,z6]),(0,[z74,z0,z1,z2,z3,z4,z6]),(0,[z423,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z424,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z58,z30]),(0,[z0,z1,z2,z114,z4,z113,z6]),(1,[z0,z1,z2,z3,z81,z6]),(0,[z0,z1,z2,z381,z3,z4,z6])],[(0,[z0,z1,z2,z425,z3,z4,z6]),(0,[z426,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z9,z2,z3,z49,z4])]],
   [[(0,[z0,z1,z427,z2,z3,z4,z6]),(0,[z36,z0,z1,z2,z112,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z428]),(0,[z69,z0,z1,z2,z3,z4,z30])],[(0,[z358,z0,z1,z2,z3,z4,z6]),(0,[z48,z0,z1,z2,z3,z4,z8]),(0,[z36,z0,z1,z2,z3,z4,z58]),(0,[z0,z1,z2,z3,z4,z429,z6]),(0,[z0,z430,z1,z2,z3,z4,z6]),(0,[z69,z36,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z431,z4,z6]),(0,[z36,z0,z1,z2,z3,z4,z8]),(0,[z432,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z307,z6]),(0,[z69,z0,z1,z2,z57,z4,z6])],[(0,[z0,z1,z2,z3,z224,z4,z6]),(1,[z74,z0,z1,z75,z4,z6])],[(1,[z0,z1,z2,z3,z420,z6]),(0,[z0,z1,z2,z3,z433,z4,z6]),(0,[z83,z36,z0,z1,z2,z3,z4])],[(0,[z84,z0,z1,z2,z56,z4,z6]),(0,[z434,z0,z1,z2,z3,z4,z6]),(0,[z100,z0,z1,z2,z3,z4,z30]),(0,[z0,z1,z435,z2,z3,z4,z6])],[(0,[z151,z358,z1,z2,z3,z4,z6]),(0,[z436,z0,z1,z2,z3,z4,z6]),(0,[z48,z0,z1,z2,z3,z7,z4]),(0,[z437,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z157,z62,z3,z4,z6]),(0,[z438,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z439]),(0,[z0,z1,z2,z440,z3,z4,z6])]],
   [[(0,[z441,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z442,z2,z3,z4,z6]),(0,[z0,z1,z2,z112,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z443]),(0,[z69,z0,z1,z2,z3,z4,z93])],[(0,[z0,z444,z1,z2,z3,z4,z6]),(0,[z445,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z122,z117,z6]),(0,[z446,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z447]),(0,[z448,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z180,z6]),(0,[z19,z1,z2,z3,z4,z6,z20])],[(0,[z0,z1,z2,z3,z449,z4,z6]),(0,[z0,z1,z34,z2,z3,z122,z4]),(0,[z48,z0,z160,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z450,z4,z6]),(0,[z36,z0,z1,z451,z2,z3,z4])],[(0,[z0,z1,z2,z3,z452,z4,z6]),(0,[z358,z1,z116,z2,z3,z4,z6]),(0,[z0,z1,z9,z2,z3,z58,z6]),(0,[z0,z1,z2,z3,z453,z4,z6]),(0,[z0,z1,z2,z3,z4,z81,z6]),(0,[z0,z1,z2,z454,z3,z4,z6])],[(0,[z72,z100,z0,z1,z2,z3,z6]),(0,[z0,z1,z455,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z456,z4,z6]),(0,[z0,z1,z2,z3,z457,z4,z6])],[(0,[z0,z1,z458,z2,z3,z4,z6]),(0,[z29,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z459,z3,z4,z6]),(0,[z0,z460,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z461,z4,z6])]],
   [[(0,[z298,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z361,z3,z4,z6])],[(0,[z462,z0,z1,z2,z3,z4,z6]),(0,[z100,z73,z0,z1,z2,z3,z6]),(1,[z36,z0,z1,z2,z3,z4])],[(0,[z151,z0,z1,z2,z3,z4,z30]),(0,[z0,z1,z2,z3,z463,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z464]),(0,[z0,z1,z115,z2,z75,z4,z6]),(0,[z0,z1,z2,z3,z4,z465,z6])],[(0,[z77,z1,z2,z78,z3,z4,z6]),(0,[z72,z0,z1,z2,z3,z4,z288]),(0,[z0,z1,z2,z3,z4,z6,z466]),(0,[z0,z1,z2,z3,z467,z4,z6])],[(0,[z98,z0,z26,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z468]),(0,[z0,z1,z2,z469,z3,z4,z6]),(0,[z36,z0,z1,z2,z62,z3,z4]),(0,[z470,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z471,z3,z4,z6]),(1,[z0,z1,z107,z3,z4,z6]),(0,[z0,z1,z2,z3,z472,z4,z6]),(0,[z165,z0,z1,z2,z3,z4,z30]),(0,[z473,z0,z1,z2,z3,z4,z6]),(0,[z0,z160,z2,z3,z4,z6,z8]),(0,[z0,z1,z9,z2,z3,z4,z294]),(0,[z0,z1,z2,z3,z474,z4,z6])],[(0,[z77,z1,z2,z157,z3,z4,z6]),(0,[z0,z1,z2,z3,z475,z4,z6]),(0,[z0,z1,z2,z3,z10,z4,z30]),(0,[z0,z1,z2,z3,z129,z4,z30])],[(0,[z0,z1,z2,z78,z3,z4,z30]),(0,[z0,z1,z2,z476,z3,z4,z6]),(1,[z0,z1,z50,z3,z4,z51]),(0,[z170,z36,z0,z1,z2,z3,z4])]],
   [[(0,[z0,z41,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z477,z3,z4,z6]),(0,[z478,z0,z1,z2,z3,z4,z6]),(0,[z80,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z22,z3,z4]),(0,[z0,z1,z2,z112,z3,z113,z6]),(0,[z0,z1,z2,z57,z3,z4,z30])],[(0,[z0,z1,z2,z3,z479,z4,z6]),(0,[z72,z0,z1,z2,z3,z4,z30]),(0,[z84,z19,z1,z2,z3,z4,z6]),(0,[z84,z1,z2,z3,z4,z38,z6]),(0,[z0,z1,z480,z2,z3,z4,z6])],[(0,[z481,z0,z1,z2,z3,z4,z6]),(0,[z0,z482,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z483,z3,z4,z6]),(0,[z0,z484,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z485,z6]),(0,[z0,z1,z9,z2,z3,z4,z30])],[(0,[z486,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z487,z6]),(0,[z0,z1,z2,z488,z3,z4,z6]),(0,[z0,z412,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z489,z6]),(0,[z0,z1,z2,z3,z4,z288,z6]),(1,[z73,z1,z2,z3,z117,z6]),(0,[z0,z1,z2,z3,z490,z4,z6]),(0,[z0,z491,z1,z2,z3,z4,z6])],[(0,[z492,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z493,z6]),(0,[z74,z0,z1,z2,z75,z4,z6])],[(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z494,z2,z3,z4,z6]),(0,[z495,z0,z1,z2,z3,z4,z6]),(0,[z36,z0,z1,z2,z3,z4,z123])]],
   [[(0,[z0,z1,z2,z496,z3,z4,z6]),(0,[z0,z497,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z230,z3,z4,z6]),(1,[z358,z1,z116,z3,z4,z6]),(0,[z74,z400,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z113,z30])],[(1,[z0,z1,z2,z140,z4,z6])],[(0,[z151,z1,z2,z157,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z0,z1,z2,z3,z4,z498,z6]),(0,[z0,z1,z2,z3,z499,z4,z6]),(0,[z0,z1,z2,z500,z3,z4,z6]),(0,[z501,z0,z1,z2,z3,z4,z6])],[(0,[z502,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z123,z30]),(0,[z0,z1,z2,z3,z503,z4,z6]),(0,[z0,z1,z2,z3,z504,z4,z6]),(0,[z0,z1,z2,z3,z217,z4,z30])],[(0,[z0,z1,z2,z505,z3,z4,z6]),(0,[z0,z1,z506,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z6,z106]),(0,[z0,z1,z2,z3,z4,z6,z207]),(0,[z0,z1,z2,z3,z65,z4,z6])],[(0,[z0,z1,z2,z33,z3,z4,z6]),(0,[z507,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z451,z2,z3,z4,z6])],[(0,[z212,z0,z1,z2,z3,z4,z243]),(0,[z0,z1,z2,z508,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z509,z6]),(0,[z0,z1,z2,z3,z420,z4,z6]),(0,[z0,z1,z2,z3,z510,z4,z6])]],
   [[(0,[z44,z0,z1,z116,z3,z4,z6]),(0,[z0,z1,z50,z116,z3,z4,z6]),(0,[z0,z1,z2,z511,z3,z4,z6])],[(0,[z512,z0,z1,z2,z3,z4,z6]),(1,[z513,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z514,z4,z6]),(0,[z80,z0,z1,z2,z3,z113,z6])],[(0,[z0,z1,z2,z515,z3,z4,z6]),(1,[z0,z1,z2,z112,z113,z6]),(0,[z516,z0,z1,z2,z3,z4,z6]),(0,[z36,z0,z1,z2,z12,z3,z4])],[(0,[z0,z1,z2,z3,z4,z6,z517]),(0,[z0,z518,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z519,z4,z6]),(0,[z0,z1,z2,z3,z122,z4,z6]),(1,[z0,z1,z34,z2,z3,z4]),(0,[z520,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z521,z6])],[(0,[z77,z0,z1,z2,z143,z4,z6]),(0,[z0,z1,z2,z3,z117,z123,z6]),(0,[z522,z0,z1,z2,z3,z4,z6]),(0,[z100,z0,z1,z2,z3,z122,z6]),(0,[z0,z1,z2,z3,z4,z523,z6]),(0,[z524,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z157,z3,z129,z4,z6]),(0,[z0,z1,z2,z78,z4,z113,z6]),(0,[z0,z1,z2,z3,z525,z4,z6]),(0,[z526,z36,z0,z1,z2,z3,z4])],[(0,[z527,z0,z1,z2,z3,z4,z6]),(0,[z528,z0,z1,z2,z3,z4,z6]),(0,[z529,z0,z1,z2,z3,z4,z6]),(0,[z98,z0,z1,z2,z3,z123,z6]),(0,[z0,z1,z2,z3,z4,z530,z6]),(0,[z531,z0,z1,z2,z3,z4,z6]),(0,[z532,z0,z1,z2,z3,z4,z6])],[(0,[z533,z0,z1,z2,z3,z4,z6]),(0,[z72,z0,z1,z283,z3,z4,z6]),(0,[z513,z0,z1,z2,z3,z4,z6]),(0,[z74,z0,z1,z2,z233,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z534,z4,z6]),(0,[z0,z1,z2,z114,z3,z4,z6]),(0,[z0,z1,z253,z2,z3,z4,z30])],[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z535,z6]),(0,[z0,z1,z2,z3,z536,z4,z6])],[(0,[z44,z0,z1,z157,z3,z4,z6]),(0,[z0,z1,z50,z157,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z123,z30]),(0,[z0,z1,z2,z3,z537,z4,z6]),(0,[z36,z0,z1,z2,z3,z6,z30])],[(0,[z0,z1,z2,z62,z3,z4,z30]),(1,[z0,z1,z2,z3,z58,z30]),(0,[z0,z1,z2,z3,z538,z4,z6]),(0,[z69,z0,z1,z2,z12,z4,z6]),(0,[z0,z539,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z540]),(0,[z541,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z542,z6]),(1,[z0,z141,z2,z3,z123,z6]),(0,[z0,z1,z115,z2,z3,z4,z6])],[(0,[z0,z1,z543,z2,z3,z4,z6]),(0,[z0,z544,z1,z2,z3,z4,z6]),(1,[z0,z300,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z6,z30]),(0,[z0,z1,z50,z3,z4,z6,z51])],[(0,[z36,z0,z1,z26,z2,z3,z4]),(0,[z0,z1,z2,z3,z545,z4,z6]),(0,[z36,z0,z41,z1,z2,z3,z4]),(0,[z546,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z547,z3,z4,z6])],[(1,[z326,z0,z1,z2,z3,z4]),(0,[z548,z0,z1,z2,z3,z4,z6]),(1,[z0,z160,z2,z3,z4,z8]),(1,[z128,z0,z1,z3,z129,z4])]],
   [[(0,[z0,z1,z2,z3,z7,z4,z20])],[(0,[z0,z1,z549,z2,z3,z4,z6]),(0,[z84,z0,z1,z256,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z30,z8]),(0,[z0,z1,z2,z3,z4,z6,z550]),(0,[z36,z0,z1,z2,z3,z4,z6])],[(0,[z36,z0,z109,z1,z2,z3,z4]),(1,[z0,z1,z2,z353,z4,z6]),(0,[z0,z1,z2,z12,z78,z4,z6]),(0,[z0,z1,z2,z3,z7,z4,z38]),(0,[z393,z0,z1,z2,z3,z4,z6])],[(0,[z212,z0,z109,z2,z3,z4,z6]),(0,[z0,z1,z2,z2,z3,z4,z6]),(1,[z77,z1,z2,z78,z4,z6]),(0,[z0,z1,z551,z2,z3,z4,z6]),(0,[z399,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z552,z3,z4,z6])],[(0,[z398,z0,z1,z2,z3,z4,z6]),(0,[z212,z25,z1,z2,z3,z4,z6]),(0,[z36,z0,z1,z2,z78,z3,z4]),(0,[z165,z0,z2,z3,z43,z4,z6]),(0,[z0,z553,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z122,z4,z416]),(0,[z0,z1,z2,z554,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z555]),(0,[z0,z1,z2,z556,z3,z4,z6])],[(0,[z0,z1,z2,z557,z3,z4,z6]),(0,[z44,z0,z1,z2,z3,z4,z30]),(0,[z0,z1,z50,z2,z3,z4,z30])],[(1,[z0,z1,z2,z88,z4,z6]),(0,[z212,z0,z1,z2,z88,z4,z6]),(1,[z212,z26,z2,z3,z4,z6]),(0,[z19,z0,z1,z2,z3,z4,z30]),(0,[z0,z1,z2,z3,z4,z6,z558]),(0,[z0,z1,z559,z2,z3,z4,z6]),(0,[z44,z36,z0,z1,z2,z3,z4]),(0,[z80,z0,z1,z2,z114,z4,z6]),(0,[z0,z1,z2,z12,z4,z6,z93])],[(0,[z72,z0,z300,z2,z3,z4,z6]),(0,[z19,z36,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z560,z4,z6]),(0,[z0,z1,z2,z3,z75,z4,z30])]],
   [[(0,[z0,z1,z2,z57,z143,z4,z6]),(0,[z72,z0,z1,z2,z3,z117,z6]),(0,[z0,z1,z2,z561,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z562,z6]),(0,[z563,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z57,z3,z4])],[(0,[z1,z2,z78,z3,z143,z4,z6]),(0,[z0,z1,z2,z3,z564,z4,z6]),(1,[z0,z1,z2,z3,z565,z6]),(0,[z0,z1,z2,z409,z3,z4,z6])],[(0,[z0,z1,z2,z566,z3,z4,z6])],[(0,[z0,z1,z2,z3,z567,z4,z6])],[(0,[z0,z1,z2,z3,z4,z568,z6]),(0,[z0,z569,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z143,z4,z6]),(0,[z0,z1,z2,z570,z3,z4,z6]),(0,[z0,z1,z2,z3,z571,z4,z6]),(0,[z0,z1,z233,z3,z75,z4,z6]),(0,[z0,z1,z2,z572,z3,z4,z6]),(0,[z0,z573,z1,z2,z3,z4,z6])],[(0,[z25,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z574,z3,z4,z6]),(0,[z0,z1,z2,z575,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z576]),(0,[z0,z141,z2,z3,z4,z123,z6]),(0,[z0,z1,z2,z3,z58,z6,z30]),(0,[z0,z1,z2,z114,z3,z4,z428])],[(0,[z577,z0,z1,z2,z3,z4,z6]),(0,[z72,z0,z239,z2,z3,z4,z6]),(0,[z578,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z579,z6])]],
   [[(0,[z29,z0,z1,z105,z3,z4,z6]),(0,[z77,z0,z1,z2,z3,z4,z30]),(0,[z580,z0,z1,z2,z3,z4,z6])],[(0,[z77,z36,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z581,z4,z6]),(0,[z582,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z241]),(0,[z100,z36,z0,z1,z2,z3,z4])],[(0,[z151,z0,z1,z157,z3,z4,z6]),(0,[z0,z1,z2,z3,z583,z4,z6]),(0,[z0,z1,z2,z3,z117,z4,z30]),(0,[z84,z0,z1,z2,z3,z4,z30]),(0,[z61,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z584,z6]),(0,[z36,z0,z1,z2,z3,z7,z4]),(0,[z0,z1,z2,z3,z4,z30,z439])],[(1,[z0,z1,z2,z3,z4,z134]),(0,[z0,z1,z2,z585,z3,z4,z6]),(0,[z586,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z587,z4,z6]),(0,[z98,z0,z1,z2,z3,z4,z30]),(0,[z183,z0,z1,z2,z3,z75,z4])],[(0,[z588,z0,z1,z2,z3,z4,z6]),(0,[z128,z0,z1,z3,z129,z4,z6]),(0,[z100,z0,z1,z2,z3,z65,z6])],[(0,[z280,z0,z1,z2,z3,z4,z6]),(1,[z73,z0,z1,z2,z3,z30]),(0,[z0,z1,z2,z3,z4,z6,z258]),(0,[z0,z1,z2,z589,z3,z4,z6]),(0,[z0,z1,z2,z3,z565,z4,z6]),(0,[z0,z1,z2,z3,z590,z4,z6]),(0,[z0,z1,z2,z114,z112,z3,z6]),(0,[z0,z281,z1,z2,z3,z4,z6])],[(0,[z591,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z592,z3,z4,z6]),(0,[z29,z0,z1,z138,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z106]),(0,[z0,z1,z593,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z308,z4,z6])]],
   [[(1,[z72,z0,z1,z2,z3,z30]),(0,[z0,z1,z2,z3,z594,z4,z6]),(0,[z0,z1,z2,z595,z3,z4,z6]),(0,[z36,z0,z1,z2,z33,z3,z4]),(0,[z0,z160,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z596,z4,z6]),(0,[z286,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z597,z2,z3,z4,z6]),(0,[z0,z1,z598,z2,z3,z4,z6]),(0,[z599,z0,z1,z2,z3,z4,z6])],[(0,[z212,z0,z26,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z600]),(0,[z0,z1,z2,z3,z601,z4,z6]),(0,[z0,z1,z2,z3,z4,z295,z6])],[(0,[z0,z1,z2,z3,z602,z4,z6]),(0,[z603,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z604,z3,z4,z6]),(0,[z36,z0,z1,z115,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z6,z605]),(1,[z0,z1,z2,z181,z4,z6]),(0,[z0,z141,z1,z2,z3,z123,z6]),(0,[z0,z1,z2,z606,z3,z4,z6])],[(0,[z607,z0,z1,z2,z3,z4,z6]),(0,[z0,z42,z2,z62,z3,z4,z6]),(0,[z608,z0,z1,z2,z3,z4,z6]),(1,[z412,z1,z2,z3,z4,z6]),(0,[z0,z1,z609,z2,z3,z4,z6])],[(0,[z151,z36,z0,z1,z2,z3,z4]),(0,[z0,z1,z157,z3,z75,z4,z6]),(0,[z0,z1,z2,z3,z4,z610,z6]),(1,[z19,z1,z2,z3,z4,z20]),(0,[z0,z1,z2,z611,z3,z4,z6]),(0,[z100,z0,z1,z2,z114,z3,z6])],[(0,[z0,z1,z612,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z122,z6,z106]),(0,[z0,z1,z2,z3,z117,z4,z330]),(0,[z0,z1,z2,z613,z3,z4,z6]),(0,[z614,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z212,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z6]),(0,[z0,z109,z1,z2,z3,z4,z6]),(0,[z0,z1,z615,z2,z3,z4,z6]),(0,[z0,z1,z2,z616,z3,z4,z6])],[(0,[z165,z36,z0,z1,z2,z3,z4]),(0,[z617,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z294])],[(0,[z0,z1,z115,z233,z3,z4,z6])],[(0,[z0,z1,z2,z3,z618,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z619]),(0,[z36,z0,z1,z2,z3,z75,z4])],[(0,[z0,z620,z1,z2,z3,z4,z6]),(0,[z0,z621,z1,z2,z3,z4,z6]),(0,[z622,z0,z1,z2,z3,z4,z6]),(0,[z98,z0,z141,z2,z3,z4,z6]),(0,[z0,z141,z1,z2,z3,z175,z4]),(0,[z0,z160,z1,z2,z3,z4,z8]),(0,[z128,z0,z1,z2,z3,z4,z30])],[(0,[z0,z1,z2,z157,z3,z4,z30]),(0,[z0,z1,z42,z2,z3,z4,z6]),(0,[z100,z36,z0,z1,z2,z3,z6])],[(0,[z0,z623,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z233,z78,z4,z6]),(0,[z72,z36,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z290,z75,z4]),(0,[z0,z1,z2,z3,z10,z4,z6]),(1,[z0,z1,z2,z3,z4,z387])],[(0,[z0,z1,z2,z3,z624,z4,z6]),(0,[z326,z0,z1,z2,z3,z117,z4]),(0,[z0,z1,z2,z3,z4,z6,z30])]],
   [[(0,[z0,z1,z2,z3,z625,z4,z6]),(1,[z98,z0,z2,z3,z122,z6]),(0,[z626,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z627,z3,z4,z6])],[(0,[z358,z0,z1,z116,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z628,z6]),(0,[z0,z1,z2,z3,z629,z4,z6]),(0,[z0,z630,z1,z2,z3,z4,z6]),(0,[z0,z141,z1,z2,z3,z4,z258]),(0,[z0,z160,z1,z2,z3,z7,z4]),(0,[z0,z1,z2,z233,z3,z4,z6]),(0,[z0,z1,z2,z3,z65,z6,z30])],[(1,[z25,z109,z2,z3,z4,z6]),(0,[z631,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z632,z3,z4,z6]),(0,[z0,z1,z2,z57,z4,z6,z93])],[(0,[z0,z1,z2,z633,z3,z4,z6]),(0,[z36,z73,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z634,z4,z6]),(0,[z0,z1,z2,z635,z3,z4,z6]),(0,[z636,z0,z1,z2,z3,z4,z6])],[(0,[z212,z1,z26,z2,z3,z4,z6]),(0,[z0,z1,z2,z637,z3,z4,z6]),(1,[z0,z1,z222,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z38,z6]),(0,[z0,z1,z638,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z639,z4,z6]),(0,[z0,z640,z1,z2,z3,z4,z6]),(0,[z0,z641,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z10,z4,z387]),(0,[z0,z1,z2,z57,z3,z4,z93])],[(0,[z0,z1,z642,z2,z3,z4,z6]),(0,[z334,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z643,z3,z4,z6])],[(0,[z0,z1,z2,z644,z3,z4,z6]),(0,[z0,z1,z115,z2,z233,z4,z6])],[(0,[z0,z645,z1,z2,z3,z4,z6]),(0,[z29,z0,z1,z2,z143,z4,z6]),(0,[z0,z32,z2,z33,z3,z4,z6]),(0,[z0,z1,z2,z3,z122,z6,z30]),(0,[z0,z1,z2,z112,z3,z4,z241]),(0,[z0,z1,z2,z3,z4,z6,z93])]],
   [[(0,[z646,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z647,z2,z3,z4,z6]),(0,[z0,z1,z2,z648,z3,z4,z6]),(0,[z0,z1,z2,z3,z649,z4,z6])],[(0,[z650,z0,z1,z2,z3,z4,z6]),(0,[z651,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z416]),(0,[z0,z1,z3,z129,z4,z6,z51]),(0,[z396,z0,z1,z2,z3,z4,z30])],[(1,[z0,z1,z2,z3,z4,z243]),(0,[z0,z1,z2,z3,z123,z6,z106]),(0,[z0,z1,z652,z2,z3,z4,z6]),(1,[z0,z1,z9,z3,z58,z6]),(0,[z100,z0,z1,z2,z3,z10,z6])],[(0,[z358,z0,z1,z157,z3,z4,z6]),(0,[z653,z0,z1,z2,z3,z4,z6])],[(0,[z25,z0,z109,z2,z3,z4,z6]),(1,[z151,z1,z157,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z330]),(0,[z0,z654,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z38,z6,z20]),(0,[z61,z0,z41,z2,z3,z4,z6]),(0,[z0,z1,z2,z114,z3,z6,z30])],[(0,[z0,z1,z116,z2,z3,z4,z6]),(1,[z72,z1,z2,z3,z6,z106]),(0,[z0,z1,z2,z3,z655,z4,z6]),(0,[z0,z1,z656,z2,z3,z4,z6]),(0,[z0,z1,z657,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z658,z4,z6]),(0,[z0,z1,z2,z659,z3,z4,z6])],[(0,[z0,z1,z26,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z660,z6]),(0,[z0,z661,z1,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z4,z30]),(0,[z0,z662,z1,z2,z3,z4,z6]),(0,[z0,z1,z50,z2,z3,z565,z6]),(1,[z0,z1,z2,z3,z4,z428])],[(0,[z72,z0,z1,z2,z140,z4,z6]),(0,[z0,z1,z256,z2,z3,z4,z6]),(0,[z0,z1,z663,z2,z3,z4,z6]),(1,[z0,z1,z2,z361,z3,z6])]],
   [[(0,[z664,z0,z1,z2,z3,z4,z6]),(0,[z665,z0,z1,z2,z3,z4,z6]),(0,[z666,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z667,z4,z6]),(0,[z0,z1,z2,z3,z668,z4,z6]),(1,[z0,z1,z2,z259,z4,z6]),(0,[z0,z1,z2,z3,z4,z38,z8]),(0,[z513,z0,z1,z2,z3,z38,z6]),(0,[z669,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z670,z3,z4,z6]),(0,[z0,z1,z671,z2,z3,z4,z6]),(0,[z0,z1,z3,z10,z4,z58,z6]),(0,[z0,z1,z2,z401,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z672]),(0,[z673,z0,z1,z2,z3,z4,z6]),(0,[z80,z0,z1,z2,z143,z4,z6]),(0,[z674,z0,z1,z2,z3,z4,z6]),(0,[z675,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z161,z6]),(0,[z676,z0,z1,z2,z3,z4,z6])],[(0,[z677,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z678,z4,z6]),(0,[z0,z32,z1,z2,z3,z4,z6]),(0,[z0,z141,z1,z2,z3,z4,z30]),(0,[z74,z0,z1,z2,z3,z4,z30]),(0,[z679,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z50,z2,z3,z307,z6])],[(0,[z0,z1,z211,z2,z3,z4,z6]),(0,[z680,z0,z1,z2,z3,z4,z6]),(1,[z165,z0,z2,z43,z4,z6]),(0,[z0,z1,z2,z3,z681,z4,z6]),(0,[z98,z0,z1,z2,z3,z122,z6]),(0,[z682,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z683,z6]),(0,[z0,z1,z684,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z201,z6]),(0,[z61,z0,z1,z42,z3,z4,z6]),(0,[z44,z0,z1,z9,z3,z4,z6]),(0,[z526,z0,z1,z2,z3,z4,z6])],[(0,[z685,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z686,z4,z6])],[(1,[z0,z1,z2,z3,z4,z70]),(0,[z212,z0,z1,z2,z3,z4,z70]),(0,[z358,z0,z1,z2,z3,z4,z30]),(0,[z0,z1,z2,z687,z3,z4,z6]),(0,[z688,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z689,z3,z4,z6]),(0,[z0,z1,z2,z3,z690,z4,z6]),(0,[z0,z1,z691,z2,z3,z4,z6]),(0,[z0,z247,z1,z2,z3,z4,z6])],[(0,[z358,z36,z0,z1,z2,z3,z4]),(0,[z692,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z693,z2,z3,z4,z6]),(0,[z0,z694,z1,z2,z3,z4,z6]),(0,[z0,z1,z50,z2,z3,z129,z4]),(0,[z0,z1,z2,z3,z4,z113,z6])]],
   [[(0,[z695,z0,z1,z2,z3,z4,z6]),(0,[z696,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z56,z3,z4,z6])],[(0,[z0,z1,z2,z143,z4,z113,z6]),(0,[z0,z1,z2,z697,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z698,z6]),(0,[z0,z1,z2,z3,z4,z123,z6]),(0,[z0,z1,z2,z3,z123,z6,z30]),(0,[z0,z1,z2,z699,z3,z4,z6])],[(0,[z0,z700,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z701,z3,z4,z6])],[(0,[z0,z1,z2,z138,z3,z4,z6]),(1,[z400,z1,z2,z3,z4,z6]),(0,[z69,z0,z1,z2,z12,z3,z4]),(0,[z0,z1,z2,z440,z3,z4,z30])],[(0,[z702,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z703,z2,z3,z4,z6]),(0,[z0,z1,z2,z112,z3,z4,z30]),(0,[z0,z1,z2,z3,z4,z6,z269])],[(0,[z704,z0,z1,z2,z3,z4,z6])],[(0,[z25,z109,z1,z2,z3,z4,z6]),(0,[z151,z0,z1,z2,z353,z4,z6]),(0,[z1,z2,z157,z3,z143,z4,z6]),(0,[z0,z1,z2,z3,z7,z4,z6]),(0,[z705,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z706,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z707,z157,z3,z4,z6]),(0,[z77,z1,z2,z648,z4,z6]),(0,[z0,z1,z2,z3,z708,z6]),(0,[z36,z0,z1,z222,z3,z4]),(0,[z0,z1,z2,z3,z4,z709])],[(0,[z0,z1,z2,z3,z4,z710]),(0,[z74,z183,z0,z1,z75,z4]),(0,[z0,z1,z2,z711,z4,z6])],[(0,[z73,z0,z1,z2,z3,z330]),(0,[z84,z1,z107,z3,z4,z38])],[(0,[z0,z1,z2,z88,z4,z70]),(0,[z212,z26,z2,z3,z4,z70]),(0,[z0,z712,z2,z3,z4,z6]),(0,[z0,z1,z713,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z714]),(0,[z0,z1,z2,z3,z715,z6])],[(0,[z0,z1,z2,z716,z4,z6]),(0,[z72,z0,z1,z2,z3,z330]),(0,[z492,z0,z1,z2,z3,z30]),(0,[z72,z1,z2,z3,z288,z106]),(0,[z0,z1,z717,z3,z4,z6])],[(0,[z718,z0,z1,z3,z4,z6]),(0,[z61,z0,z62,z3,z4,z30]),(0,[z0,z1,z2,z3,z719,z6]),(0,[z0,z1,z2,z3,z720,z6])],[(0,[z0,z1,z211,z3,z180,z6]),(0,[z0,z1,z2,z3,z721,z6]),(0,[z0,z1,z2,z283,z3,z30]),(0,[z0,z1,z2,z722,z4,z6]),(0,[z69,z0,z1,z2,z440,z4])],[(0,[z723,z0,z1,z2,z3,z180]),(0,[z0,z1,z2,z3,z237,z30]),(0,[z0,z300,z2,z3,z4,z288]),(0,[z0,z1,z2,z3,z4,z724]),(0,[z98,z0,z2,z3,z122,z6]),(0,[z0,z1,z3,z725,z4,z6]),(0,[z0,z1,z2,z12,z401,z4])]],
   [[(0,[z0,z26,z2,z3,z123,z30]),(0,[z0,z1,z2,z726,z4,z6]),(0,[z72,z0,z300,z2,z3,z30]),(0,[z36,z0,z239,z2,z3,z4]),(0,[z0,z1,z2,z3,z727,z6]),(0,[z1,z2,z3,z4,z728,z6])],[(0,[z25,z109,z2,z3,z4,z6]),(0,[z0,z1,z116,z3,z307,z6]),(0,[z0,z1,z3,z729,z4,z6])],[(0,[z0,z1,z2,z730,z3,z6]),(0,[z84,z1,z2,z3,z4,z295]),(0,[z582,z1,z2,z3,z4,z38]),(0,[z0,z1,z2,z731,z4,z6]),(0,[z0,z1,z2,z3,z161,z6]),(0,[z36,z0,z1,z2,z3,z161]),(0,[z36,z0,z1,z2,z361,z3])],[(0,[z0,z1,z2,z3,z4,z732]),(0,[z0,z1,z3,z217,z58,z30])],[(0,[z83,z526,z1,z2,z3,z4])],[(0,[z0,z1,z2,z230,z180,z6]),(0,[z0,z1,z733,z3,z4,z6]),(0,[z734,z0,z1,z2,z3,z4])],[(0,[z432,z1,z157,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z735]),(0,[z0,z300,z2,z3,z4,z30])],[(0,[z0,z239,z2,z3,z4,z288]),(0,[z0,z1,z2,z3,z681,z30]),(0,[z0,z1,z2,z736,z4,z6])]],
   [[(0,[z0,z1,z737,z3,z4,z6]),(0,[z541,z1,z157,z3,z4,z6]),(0,[z0,z1,z2,z259,z6,z30]),(0,[z0,z1,z2,z3,z4,z416]),(0,[z0,z1,z2,z3,z122,z30])],[(0,[z0,z1,z2,z3,z4,z738]),(0,[z0,z739,z2,z3,z4,z6]),(0,[z531,z1,z2,z3,z4,z20]),(0,[z0,z1,z9,z3,z58,z6])],[(0,[z0,z1,z2,z3,z4,z740]),(0,[z128,z0,z1,z3,z217,z4])],[(0,[z0,z1,z2,z230,z4,z30]),(0,[z151,z1,z157,z3,z4,z6]),(0,[z0,z1,z2,z353,z4,z30]),(0,[z0,z1,z157,z3,z307,z6]),(0,[z0,z1,z2,z3,z276,z30])],[(0,[z36,z0,z1,z2,z88,z4]),(0,[z0,z2,z3,z741,z4,z6])],[(0,[z109,z742,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z525,z30]),(0,[z73,z1,z2,z3,z295,z6]),(0,[z0,z1,z743,z3,z4,z6]),(0,[z0,z1,z3,z744,z4,z51]),(0,[z36,z0,z1,z2,z745,z4])],[(0,[z746,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z224,z4,z6]),(0,[z0,z1,z2,z3,z161,z8]),(0,[z0,z1,z253,z3,z58,z30]),(0,[z128,z0,z1,z2,z3,z81]),(0,[z0,z1,z2,z361,z3,z6])],[(0,[z305,z0,z1,z2,z3,z30]),(0,[z1,z116,z707,z3,z4,z6])]],
   [[(0,[z98,z0,z2,z3,z122,z416])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z0,z544,z2,z33,z4,z6]),(0,[z0,z1,z2,z3,z747,z30])],[(0,[z748,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z410,z30]),(0,[z0,z1,z2,z3,z749,z4]),(0,[z0,z1,z2,z3,z81,z30])],[(0,[z750,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z175,z4]),(0,[z0,z1,z2,z751,z4,z6]),(0,[z0,z2,z3,z17,z123,z30]),(0,[z0,z1,z2,z409,z113,z6])],[(0,[z0,z1,z2,z3,z752,z6]),(0,[z0,z1,z256,z181,z4,z6]),(0,[z0,z1,z3,z753,z4,z6]),(0,[z36,z0,z1,z2,z95,z3])],[(0,[z0,z1,z2,z3,z754,z6]),(0,[z0,z1,z2,z3,z122,z330]),(0,[z0,z1,z2,z3,z4,z755]),(0,[z0,z430,z1,z2,z3,z30])],[(0,[z0,z1,z251,z230,z4,z6]),(0,[z0,z1,z2,z3,z4,z756]),(0,[z0,z1,z2,z3,z307,z30]),(0,[z0,z1,z451,z3,z129,z4])],[(0,[z0,z742,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z757]),(0,[z0,z1,z2,z3,z4,z758]),(0,[z0,z1,z759,z3,z4,z6]),(0,[z0,z1,z3,z760,z4,z30])]],
   [[(0,[z0,z1,z2,z3,z4,z258]),(0,[z0,z1,z2,z3,z420,z30]),(0,[z0,z1,z2,z3,z465,z30])],[(0,[z345,z1,z116,z3,z4,z6]),(0,[z0,z1,z2,z143,z113,z30]),(0,[z36,z0,z1,z24,z2,z3]),(0,[z0,z1,z2,z3,z601,z30])],[(0,[z322,z1,z157,z3,z4,z6]),(0,[z541,z0,z1,z75,z4,z6]),(1,[z0,z1,z2,z3,z761]),(0,[z0,z1,z2,z3,z81,z93])],[(0,[z0,z1,z9,z3,z49,z58]),(0,[z128,z0,z1,z3,z744,z4])],[(0,[z0,z1,z2,z3,z180,z762]),(0,[z0,z1,z2,z763,z4,z6])],[(0,[z0,z1,z2,z3,z4,z764]),(0,[z0,z1,z2,z3,z383,z30]),(0,[z0,z1,z50,z3,z307,z51]),(0,[z0,z1,z2,z3,z308,z30])],[(0,[z0,z1,z2,z3,z180,z30]),(0,[z0,z1,z2,z3,z4,z765]),(0,[z36,z0,z1,z2,z140,z4]),(0,[z36,z0,z1,z2,z3,z594]),(0,[z766,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z78,z290,z4]),(0,[z72,z36,z1,z2,z3,z106]),(0,[z0,z1,z2,z767,z4,z30])]],
   [[(0,[z0,z1,z2,z3,z4,z768]),(0,[z0,z239,z2,z140,z4,z6]),(0,[z36,z0,z1,z2,z3,z335]),(0,[z0,z1,z2,z3,z4,z769])],[(0,[z0,z1,z2,z3,z770,z6]),(0,[z0,z1,z2,z3,z4,z771]),(0,[z0,z2,z33,z772,z4,z6]),(0,[z0,z1,z2,z3,z773,z4])],[(0,[z0,z1,z2,z3,z487,z30]),(0,[z0,z1,z2,z3,z290,z4]),(0,[z0,z1,z50,z2,z3,z81])],[(0,[z0,z1,z774,z3,z4,z6]),(0,[z0,z1,z2,z3,z5,z243]),(0,[z0,z239,z283,z3,z4,z6]),(0,[z0,z1,z2,z3,z288,z30]),(0,[z0,z1,z2,z3,z775,z6]),(0,[z0,z1,z2,z114,z3,z776])],[(0,[z0,z1,z2,z3,z777,z6]),(0,[z1,z157,z3,z224,z4,z6]),(0,[z0,z1,z2,z778,z4,z6]),(0,[z0,z1,z779,z3,z4,z6]),(0,[z72,z1,z2,z259,z6,z106]),(0,[z0,z1,z2,z3,z587,z30]),(0,[z373,z0,z1,z2,z3,z30]),(0,[z780,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z22,z3,z565]),(0,[z36,z0,z1,z781,z3,z4])],[(0,[z0,z1,z2,z3,z4,z782]),(1,[z1,z2,z783,z4,z6]),(0,[z0,z1,z2,z3,z4,z784]),(0,[z0,z1,z2,z31,z3,z30]),(0,[z0,z1,z2,z181,z4,z30]),(0,[z0,z1,z2,z3,z785,z6]),(0,[z786,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z787])],[(0,[z0,z1,z2,z788,z3,z4]),(0,[z0,z1,z2,z789,z4,z6]),(0,[z412,z1,z2,z233,z4,z6]),(0,[z790,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z791,z4,z6]),(0,[z286,z1,z2,z3,z4,z207])]],
   [[(0,[z86,z1,z157,z3,z4,z6]),(0,[z139,z0,z2,z43,z4,z6]),(0,[z0,z1,z2,z3,z4,z792]),(0,[z0,z1,z2,z3,z4,z793]),(0,[z0,z1,z2,z794,z3,z6]),(0,[z0,z1,z2,z112,z113,z241]),(0,[z0,z1,z2,z795,z4,z6])],[(0,[z0,z1,z251,z3,z180,z6]),(0,[z0,z1,z104,z2,z3,z30]),(0,[z0,z1,z107,z3,z4,z30]),(0,[z36,z0,z1,z2,z3,z420])],[(0,[z614,z1,z157,z3,z4,z6]),(0,[z358,z1,z707,z3,z4,z6]),(0,[z0,z1,z2,z3,z796,z6]),(1,[z0,z2,z3,z741,z6]),(0,[z136,z0,z1,z2,z3,z30])],[(0,[z0,z1,z2,z3,z4,z797])],[(0,[z380,z1,z2,z78,z4,z6]),(0,[z0,z1,z2,z3,z4,z798]),(0,[z0,z1,z799,z3,z4,z6]),(0,[z0,z1,z800,z2,z3,z122]),(0,[z0,z1,z2,z801,z4,z6])],[(0,[z0,z1,z2,z3,z802,z4]),(0,[z0,z1,z2,z3,z509,z30]),(0,[z69,z0,z1,z2,z795,z4])],[(0,[z750,z0,z1,z2,z3,z5]),(0,[z0,z160,z155,z2,z3,z4]),(0,[z74,z400,z1,z75,z4,z6]),(0,[z0,z1,z2,z3,z4,z803])],[(0,[z0,z1,z2,z3,z4,z804]),(0,[z0,z1,z2,z3,z4,z805]),(0,[z0,z1,z2,z3,z5,z70]),(0,[z680,z1,z157,z3,z4,z6]),(0,[z0,z1,z2,z140,z4,z288]),(0,[z166,z0,z1,z2,z3,z201])]],
   [[(0,[z36,z0,z1,z2,z224,z4]),(0,[z0,z1,z2,z806,z4,z6]),(0,[z0,z1,z2,z483,z3,z30]),(0,[z0,z1,z807,z3,z4,z30])],[(0,[z0,z1,z2,z808,z4,z6]),(0,[z73,z1,z2,z3,z117,z30]),(0,[z809,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z810,z3,z30])],[(0,[z0,z1,z211,z88,z4,z6]),(0,[z212,z26,z211,z3,z4,z6]),(1,[z742,z2,z3,z4,z6]),(0,[z0,z28,z2,z3,z123,z6]),(0,[z0,z1,z2,z3,z4,z811]),(1,[z0,z300,z2,z3,z30]),(0,[z100,z0,z1,z2,z259,z6]),(0,[z0,z1,z2,z3,z4,z812]),(0,[z0,z1,z2,z3,z813,z6]),(0,[z44,z0,z1,z3,z10,z6]),(0,[z0,z1,z2,z111,z3,z4])],[(0,[z0,z1,z2,z814,z4,z6]),(0,[z0,z1,z815,z3,z4,z6]),(0,[z524,z1,z2,z78,z4,z6]),(0,[z0,z1,z2,z3,z4,z816]),(0,[z0,z1,z2,z3,z390,z30]),(0,[z0,z1,z2,z3,z129,z307]),(0,[z0,z1,z2,z381,z3,z30])],[(0,[z0,z1,z817,z3,z4,z6]),(0,[z0,z1,z818,z3,z4,z6]),(0,[z0,z1,z2,z819,z4,z6]),(0,[z0,z1,z2,z3,z530,z30])],[(0,[z358,z1,z116,z3,z4,z30]),(0,[z0,z1,z2,z3,z820,z6]),(0,[z74,z412,z1,z75,z4,z6]),(0,[z0,z1,z2,z3,z4,z821]),(0,[z36,z0,z1,z2,z3,z81]),(0,[z298,z0,z1,z381,z3,z4])],[(0,[z0,z822,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z823,z6]),(0,[z0,z1,z2,z140,z4,z30]),(0,[z513,z0,z1,z2,z3,z288]),(0,[z0,z1,z824,z3,z4,z30])],[(0,[z0,z109,z2,z3,z5,z6]),(0,[z72,z0,z1,z222,z3,z30]),(0,[z0,z825,z2,z3,z4,z6]),(0,[z826,z0,z1,z2,z3,z30])]],
   [[(0,[z0,z827,z1,z2,z3,z6]),(0,[z548,z109,z2,z3,z4,z6]),(0,[z0,z1,z138,z3,z4,z6]),(0,[z100,z0,z1,z283,z3,z6]),(0,[z44,z0,z1,z3,z10,z387])],[(0,[z0,z828,z2,z3,z4,z6]),(0,[z0,z1,z2,z143,z81,z6]),(0,[z84,z1,z2,z181,z4,z38]),(0,[z0,z2,z3,z773,z4,z6]),(0,[z36,z0,z1,z2,z3,z30])],[(0,[z0,z1,z2,z88,z5,z6]),(0,[z212,z26,z2,z3,z5,z6]),(0,[z29,z1,z2,z143,z4,z6]),(0,[z0,z1,z829,z3,z4,z6]),(0,[z0,z1,z2,z3,z830,z6]),(0,[z100,z826,z0,z1,z2,z3])],[],[(0,[z0,z1,z2,z831,z4,z6]),(0,[z0,z1,z2,z3,z4,z832]),(0,[z0,z1,z157,z3,z58,z30]),(0,[z0,z833,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z834,z6]),(0,[z0,z1,z2,z3,z92,z30]),(0,[z0,z1,z2,z3,z391,z30]),(0,[z0,z1,z835,z3,z4,z6])],[(0,[z84,z1,z2,z3,z4,z38]),(0,[z513,z0,z1,z2,z3,z30]),(0,[z36,z0,z1,z2,z3,z307])],[(0,[z742,z26,z2,z3,z4,z6]),(0,[z25,z742,z2,z3,z4,z6]),(0,[z836,z0,z1,z2,z3,z4]),(0,[z73,z1,z2,z3,z117,z330]),(0,[z837,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z838]),(0,[z0,z1,z2,z112,z113,z30])],[]],
   [[(0,[z412,z1,z3,z75,z4,z6]),(0,[z0,z1,z839,z2,z3,z290]),(0,[z0,z1,z2,z3,z10,z294])],[(0,[z0,z840,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z841,z6]),(0,[z170,z0,z1,z2,z3,z81])],[(0,[z842,z1,z2,z3,z4,z6]),(0,[z36,z0,z1,z2,z112,z113])],[(0,[z358,z1,z347,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z843]),(0,[z0,z32,z2,z772,z4,z6]),(0,[z0,z1,z34,z2,z3,z420]),(0,[z36,z412,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z417,z30]),(0,[z183,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z57,z3,z307])],[(0,[z0,z2,z3,z773,z4,z8]),(0,[z170,z0,z1,z2,z3,z30])],[(0,[z0,z1,z251,z3,z4,z243]),(0,[z844,z0,z1,z2,z4,z6]),(0,[z0,z1,z3,z845,z4,z6]),(0,[z36,z0,z1,z283,z3,z4]),(0,[z0,z1,z846,z2,z3,z4]),(0,[z0,z1,z2,z3,z10,z30]),(0,[z126,z0,z1,z2,z3,z30]),(0,[z0,z1,z847,z3,z4,z6])],[(0,[z0,z1,z2,z3,z848,z4]),(0,[z173,z1,z116,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z849]),(0,[z0,z1,z2,z3,z201,z6]),(0,[z0,z141,z2,z3,z123,z30])],[(0,[z0,z1,z2,z850,z4,z6]),(0,[z0,z239,z2,z3,z4,z134]),(0,[z0,z1,z2,z3,z851,z6]),(0,[z0,z412,z1,z75,z4,z6])],[(0,[z0,z1,z2,z852,z4,z6]),(0,[z0,z1,z853,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z854]),(0,[z462,z0,z1,z2,z3,z30]),(0,[z151,z36,z1,z157,z3,z4]),(0,[z0,z1,z283,z140,z4,z6]),(0,[z0,z1,z781,z3,z4,z6])],[(0,[z0,z1,z211,z3,z4,z6]),(0,[z0,z1,z2,z88,z180,z6]),(0,[z0,z1,z2,z3,z761,z6]),(0,[z0,z1,z2,z855,z3,z4]),(0,[z0,z1,z2,z856,z4,z6])],[(0,[z98,z0,z2,z3,z199,z6]),(0,[z0,z857,z2,z3,z4,z6]),(0,[z0,z1,z2,z783,z4,z6]),(0,[z1,z2,z3,z6,z858,z106]),(0,[z0,z1,z2,z859,z4,z6]),(0,[z0,z1,z2,z860,z4,z6])],[(0,[z0,z26,z2,z3,z5,z6]),(0,[z0,z1,z2,z861,z4,z6]),(0,[z0,z1,z862,z3,z4,z6]),(0,[z79,z0,z1,z2,z3,z30])],[(0,[z36,z0,z1,z105,z3,z4]),(0,[z77,z1,z2,z78,z4,z30]),(0,[z72,z1,z2,z3,z30,z106]),(0,[z0,z621,z2,z3,z123,z6]),(0,[z0,z1,z3,z744,z4,z6]),(0,[z80,z0,z1,z2,z114,z30]),(0,[z0,z1,z863,z3,z4,z30])]],
   [[(0,[z0,z1,z2,z864,z3,z6]),(0,[z438,z1,z2,z143,z4,z6]),(0,[z0,z1,z2,z865,z4,z6]),(0,[z0,z1,z2,z3,z431,z30]),(0,[z0,z1,z2,z3,z49,z4])],[(0,[z0,z1,z2,z3,z308,z4]),(0,[z0,z1,z2,z12,z795,z4])],[(0,[z0,z1,z2,z88,z4,z30]),(0,[z212,z26,z2,z3,z4,z30]),(0,[z36,z0,z1,z138,z3,z4]),(0,[z866,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z572,z3,z30]),(0,[z280,z1,z2,z3,z4,z295])],[(0,[z0,z1,z2,z230,z4,z6]),(0,[z445,z0,z1,z2,z3,z30]),(0,[z0,z1,z34,z2,z3,z30]),(0,[z0,z1,z435,z3,z10,z6]),(0,[z166,z247,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z867,z6]),(0,[z1,z2,z3,z117,z6,z858]),(0,[z0,z1,z2,z3,z201,z8]),(0,[z0,z1,z2,z3,z4,z868])],[(0,[z0,z1,z2,z869,z4,z6]),(0,[z19,z0,z1,z2,z3,z201]),(0,[z0,z1,z2,z3,z565,z30])],[(0,[z0,z239,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z199,z30]),(0,[z98,z0,z2,z3,z741,z6]),(0,[z100,z0,z1,z34,z2,z3]),(0,[z870,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z241])],[(0,[z0,z1,z2,z78,z81,z6])]],
   [[(0,[z0,z1,z871,z3,z4,z6]),(0,[z0,z1,z2,z872,z3,z4]),(0,[z0,z1,z2,z361,z3,z308])],[(0,[z0,z1,z2,z3,z4,z873]),(0,[z520,z1,z116,z3,z4,z6]),(0,[z326,z73,z1,z2,z3,z117]),(0,[z0,z1,z874,z2,z3,z4]),(0,[z44,z0,z1,z22,z3,z10])],[(0,[z631,z0,z1,z75,z4,z6]),(0,[z0,z1,z2,z3,z875,z6]),(0,[z0,z1,z2,z3,z876,z6]),(0,[z0,z1,z2,z3,z4,z877]),(0,[z0,z1,z3,z10,z729,z6]),(0,[z14,z0,z1,z2,z3,z30])],[(0,[z0,z1,z256,z3,z4,z6]),(0,[z0,z300,z2,z140,z4,z6]),(0,[z0,z1,z2,z878,z3,z4]),(0,[z0,z1,z2,z3,z186,z30]),(0,[z0,z1,z2,z879,z3,z4])],[(0,[z0,z1,z2,z3,z880,z6]),(0,[z881,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z510,z30]),(0,[z0,z1,z50,z3,z565,z51]),(0,[z0,z1,z2,z882,z4,z6])],[(0,[z0,z1,z251,z88,z4,z6]),(0,[z212,z26,z251,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z883]),(0,[z884,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z538,z30])],[(0,[z0,z1,z211,z3,z4,z243]),(0,[z168,z1,z2,z143,z4,z6]),(0,[z0,z1,z2,z3,z885,z6]),(0,[z0,z300,z283,z3,z4,z6])],[(0,[z36,z0,z1,z211,z3,z4]),(0,[z0,z1,z886,z3,z4,z6]),(0,[z0,z1,z887,z3,z4,z6]),(0,[z0,z1,z2,z888,z3,z4]),(0,[z74,z0,z1,z75,z4,z6]),(0,[z334,z0,z1,z2,z3,z30]),(0,[z0,z1,z2,z3,z307,z51])]],
   [[(0,[z0,z281,z2,z3,z4,z8]),(0,[z69,z0,z1,z2,z12,z4])],[(0,[z36,z0,z1,z2,z230,z4]),(0,[z0,z1,z2,z3,z889,z4]),(0,[z77,z1,z138,z3,z4,z6]),(0,[z72,z1,z2,z3,z134,z106]),(0,[z0,z1,z890,z3,z4,z6]),(0,[z0,z1,z2,z3,z564,z30]),(0,[z0,z1,z2,z795,z57,z4])],[(0,[z0,z1,z2,z3,z891,z4]),(0,[z0,z239,z222,z3,z4,z6]),(0,[z0,z32,z2,z33,z4,z6]),(0,[z0,z1,z892,z2,z3,z4]),(0,[z82,z0,z1,z2,z127,z4])],[(0,[z0,z2,z3,z741,z123,z6]),(0,[z0,z281,z2,z3,z123,z30]),(0,[z0,z1,z2,z893,z4,z6]),(0,[z334,z0,z1,z2,z3,z307])],[(1,[z412,z1,z75,z4,z6])],[(0,[z0,z1,z894,z3,z4,z6]),(0,[z0,z1,z2,z230,z4,z243]),(0,[z151,z1,z157,z224,z4,z6]),(0,[z0,z1,z2,z3,z4,z288]),(0,[z36,z0,z422,z1,z2,z3]),(0,[z0,z1,z2,z3,z4,z761]),(0,[z0,z1,z2,z895,z4,z6]),(0,[z0,z1,z2,z882,z112,z6])],[(0,[z0,z1,z2,z3,z180,z6]),(0,[z0,z1,z2,z3,z489,z30]),(0,[z0,z518,z1,z2,z3,z30]),(0,[z896,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z897,z4,z6]),(0,[z0,z1,z2,z3,z4,z294]),(0,[z898,z1,z2,z3,z4,z30])],[(0,[z0,z1,z3,z729,z58,z6]),(0,[z0,z1,z2,z3,z113,z241])]],
   [[(0,[z36,z25,z109,z2,z3,z4]),(0,[z128,z0,z1,z556,z3,z4])],[(0,[z412,z1,z115,z3,z4,z6]),(0,[z412,z1,z2,z3,z4,z30]),(0,[z0,z899,z2,z3,z4,z6]),(0,[z36,z0,z1,z2,z3,z35])],[(0,[z0,z1,z211,z3,z4,z70]),(0,[z0,z1,z2,z3,z4,z762]),(0,[z0,z1,z2,z900,z4,z6]),(0,[z0,z1,z2,z901,z4,z6]),(0,[z72,z0,z1,z2,z3,z747]),(0,[z513,z84,z1,z2,z3,z38])],[(0,[z902,z0,z1,z2,z3,z4]),(0,[z151,z1,z707,z3,z4,z6]),(0,[z358,z36,z1,z116,z3,z4]),(0,[z72,z239,z2,z3,z6,z106]),(0,[z79,z1,z2,z3,z6,z106]),(0,[z0,z1,z2,z3,z4,z903]),(0,[z0,z2,z890,z3,z4,z6]),(0,[z100,z36,z0,z1,z2,z3]),(0,[z826,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z30]),(0,[z0,z1,z2,z3,z4,z904]),(0,[z905,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z498,z30]),(1,[z0,z2,z772,z4,z6])],[(0,[z36,z0,z1,z2,z3,z4]),(0,[z0,z144,z2,z3,z123,z6]),(0,[z0,z1,z107,z181,z4,z6]),(0,[z84,z1,z2,z56,z4,z38]),(0,[z0,z1,z2,z906,z4,z6]),(0,[z0,z1,z2,z882,z113,z6])],[(0,[z0,z1,z2,z3,z907,z6]),(0,[z0,z1,z116,z224,z4,z6]),(0,[z0,z239,z2,z259,z4,z6]),(0,[z0,z1,z2,z908,z4,z30])],[(0,[z278,z0,z1,z2,z3,z30]),(0,[z0,z300,z2,z3,z117,z6]),(0,[z0,z1,z2,z3,z123,z258]),(0,[z0,z141,z2,z3,z741,z6])]],
   [[(0,[z0,z1,z909,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z910]),(0,[z100,z0,z300,z2,z3,z6]),(0,[z165,z36,z0,z2,z43,z4]),(0,[z0,z1,z911,z3,z4,z6])],[(0,[z0,z1,z2,z230,z4,z70]),(0,[z0,z1,z222,z3,z4,z288]),(0,[z0,z1,z2,z140,z4,z134]),(0,[z0,z1,z2,z3,z912,z6]),(0,[z0,z1,z2,z795,z3,z4]),(0,[z36,z0,z1,z2,z3,z55])],[(0,[z0,z1,z2,z3,z913,z6]),(0,[z0,z1,z2,z3,z914,z6]),(0,[z0,z1,z2,z3,z4,z915])],[(0,[z0,z1,z916,z3,z4,z6]),(0,[z0,z1,z50,z3,z4,z51])],[(0,[z0,z1,z2,z917,z4,z6]),(0,[z29,z1,z105,z143,z4,z6]),(0,[z0,z1,z283,z3,z4,z134]),(0,[z98,z0,z2,z3,z122,z30]),(0,[z0,z1,z3,z725,z4,z30])],[(0,[z231,z0,z1,z2,z3,z30]),(0,[z0,z1,z2,z3,z918,z6]),(0,[z0,z1,z2,z3,z523,z30]),(0,[z1,z2,z3,z4,z728,z30])],[(0,[z25,z109,z2,z3,z4,z30]),(0,[z77,z1,z2,z783,z4,z6])],[(0,[z0,z1,z251,z3,z4,z6]),(0,[z358,z1,z2,z224,z4,z6]),(0,[z0,z1,z2,z919,z4,z6]),(0,[z0,z890,z62,z3,z4,z6]),(0,[z920,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z180,z243]),(0,[z0,z1,z222,z3,z4,z30]),(0,[z0,z1,z9,z3,z58,z294])],[(0,[z546,z1,z116,z3,z4,z6]),(0,[z73,z1,z2,z3,z117,z6]),(0,[z0,z1,z2,z3,z4,z330]),(0,[z297,z0,z2,z3,z122,z6])],[(0,[z0,z1,z2,z3,z921,z4]),(0,[z0,z1,z2,z78,z113,z30]),(0,[z0,z1,z2,z3,z535,z30]),(0,[z922,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z923]),(0,[z29,z1,z138,z143,z4,z6])],[(0,[z212,z26,z2,z230,z4,z6]),(0,[z0,z1,z2,z3,z4,z924]),(0,[z79,z26,z2,z3,z4,z6]),(0,[z0,z1,z2,z611,z3,z30])],[(0,[z358,z1,z116,z3,z4,z6]),(0,[z0,z1,z2,z259,z4,z288]),(0,[z286,z73,z1,z2,z3,z30]),(0,[z0,z1,z2,z3,z542,z30]),(0,[z0,z1,z2,z3,z925,z4]),(0,[z0,z1,z2,z3,z113,z30])],[(0,[z0,z1,z2,z140,z4,z6]),(0,[z0,z1,z824,z3,z4,z6]),(0,[z0,z1,z2,z3,z354,z30]),(0,[z0,z1,z9,z3,z58,z30])],[(0,[z0,z1,z2,z3,z4,z926]),(0,[z0,z1,z2,z3,z686,z30]),(0,[z0,z1,z2,z3,z776,z30]),(0,[z0,z1,z2,z409,z4,z93])]],
   [[(0,[z0,z1,z2,z3,z927,z6]),(0,[z0,z1,z2,z3,z928,z4]),(0,[z0,z1,z2,z929,z4,z6]),(0,[z151,z1,z157,z3,z4,z30])],[(0,[z0,z1,z283,z3,z4,z6]),(0,[z930,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z931,z4])],[(0,[z72,z0,z239,z2,z3,z30]),(0,[z73,z1,z2,z3,z295,z30]),(0,[z0,z160,z2,z3,z420,z8])],[(0,[z318,z0,z1,z75,z4,z6]),(0,[z0,z1,z2,z3,z4,z932]),(0,[z36,z0,z1,z2,z259,z4]),(0,[z0,z216,z1,z2,z3,z30]),(0,[z0,z1,z2,z361,z3,z30])],[(0,[z0,z1,z2,z3,z180,z70]),(0,[z0,z300,z2,z3,z4,z134]),(0,[z0,z1,z2,z259,z4,z30]),(0,[z36,z0,z1,z107,z3,z4]),(0,[z933,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z934,z4]),(0,[z0,z1,z2,z22,z3,z30])],[(0,[z0,z1,z2,z3,z4,z935]),(0,[z0,z1,z2,z936,z3,z4]),(0,[z72,z0,z1,z283,z3,z30]),(0,[z513,z0,z1,z2,z3,z6]),(0,[z73,z1,z2,z3,z6,z858]),(0,[z84,z1,z2,z3,z38,z201]),(0,[z0,z1,z2,z204,z3,z30])],[(0,[z0,z1,z2,z3,z4,z937]),(0,[z938,z0,z1,z2,z3,z4]),(1,[z1,z2,z3,z4,z903]),(0,[z36,z0,z1,z2,z3,z201])],[(0,[z0,z332,z1,z2,z3,z30]),(0,[z0,z1,z2,z939,z4,z6]),(0,[z0,z1,z2,z3,z940,z6]),(0,[z72,z1,z2,z3,z6,z858]),(0,[z72,z221,z1,z2,z3,z6]),(0,[z165,z0,z2,z43,z4,z30]),(1,[z826,z0,z1,z2,z3])]],
   [[(0,[z36,z0,z1,z2,z3,z5]),(0,[z212,z36,z26,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z941]),(0,[z61,z0,z62,z3,z4,z6]),(0,[z0,z1,z942,z3,z4,z6]),(0,[z0,z1,z2,z409,z113,z30]),(0,[z0,z1,z943,z3,z4,z6])],[(0,[z0,z1,z2,z3,z944,z6]),(0,[z0,z1,z2,z3,z945,z4]),(0,[z0,z1,z2,z3,z58,z294])],[(0,[z0,z1,z222,z140,z4,z6]),(0,[z0,z946,z2,z3,z4,z6]),(0,[z0,z1,z839,z2,z3,z6]),(0,[z86,z0,z1,z2,z3,z30]),(0,[z0,z1,z2,z3,z457,z30])],[(0,[z0,z1,z256,z56,z4,z6]),(0,[z0,z1,z2,z3,z246,z30])],[(0,[z0,z1,z947,z3,z4,z6]),(0,[z0,z1,z948,z3,z4,z6]),(0,[z0,z663,z2,z3,z123,z6]),(0,[z0,z1,z2,z3,z4,z949])],[(0,[z0,z1,z2,z950,z4,z6]),(0,[z1,z2,z78,z783,z4,z6]),(0,[z61,z36,z0,z62,z3,z4]),(0,[z0,z1,z2,z951,z4,z6])],[(0,[z0,z952,z2,z3,z4,z6]),(0,[z0,z953,z2,z3,z4,z6]),(0,[z0,z1,z954,z3,z4,z6]),(0,[z98,z0,z34,z2,z3,z122])],[(0,[z212,z26,z2,z3,z180,z6]),(0,[z0,z1,z2,z3,z58,z30])]],
   [[(0,[z0,z1,z2,z3,z4,z955]),(0,[z0,z1,z2,z3,z4,z956]),(0,[z0,z141,z2,z3,z123,z6]),(0,[z400,z1,z2,z3,z4,z30]),(0,[z0,z1,z2,z3,z579,z30]),(0,[z36,z0,z1,z2,z856,z4])],[(0,[z0,z300,z2,z3,z4,z6]),(0,[z0,z1,z2,z957,z4,z6]),(0,[z0,z1,z138,z143,z4,z6])],[(0,[z0,z1,z2,z958,z3,z4])],[(0,[z0,z1,z71,z3,z58,z6]),(0,[z0,z1,z2,z3,z4,z959]),(0,[z72,z1,z2,z140,z6,z106]),(0,[z0,z1,z2,z960,z4,z6]),(0,[z0,z1,z2,z3,z4,z961]),(0,[z0,z1,z2,z3,z584,z30]),(0,[z0,z160,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z962]),(0,[z0,z1,z736,z75,z4,z6]),(0,[z128,z0,z1,z3,z129,z4])],[(0,[z1,z2,z157,z224,z4,z6]),(0,[z0,z1,z2,z3,z963,z4]),(0,[z0,z1,z2,z3,z4,z964]),(0,[z0,z1,z2,z3,z4,z965]),(0,[z0,z1,z2,z3,z966,z4]),(0,[z69,z0,z1,z2,z3,z307]),(0,[z0,z1,z3,z129,z744,z4])],[(0,[z0,z1,z251,z3,z4,z70]),(0,[z0,z1,z2,z3,z967,z4]),(0,[z0,z1,z2,z3,z968,z4]),(0,[z0,z1,z2,z969,z3,z6]),(0,[z44,z36,z0,z1,z3,z10]),(0,[z0,z1,z2,z409,z4,z269])],[(0,[z0,z1,z2,z3,z970,z6]),(0,[z0,z1,z2,z353,z4,z6]),(0,[z0,z1,z2,z971,z3,z4]),(0,[z72,z1,z283,z3,z6,z106]),(0,[z972,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z973,z6]),(0,[z18,z0,z62,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z974]),(0,[z44,z0,z1,z3,z729,z6])],[(0,[z0,z1,z283,z259,z4,z6]),(0,[z0,z1,z2,z3,z975,z4]),(0,[z0,z1,z2,z976,z3,z6]),(0,[z0,z1,z253,z3,z58,z6])],[(0,[z0,z1,z2,z3,z4,z977]),(0,[z0,z1,z2,z3,z978,z6]),(0,[z74,z36,z0,z1,z75,z4])],[(0,[z0,z1,z2,z979,z4,z6]),(0,[z0,z1,z980,z3,z4,z6]),(0,[z0,z1,z981,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z982]),(0,[z0,z1,z2,z983,z4,z6]),(0,[z84,z0,z1,z2,z3,z201]),(0,[z0,z1,z2,z3,z433,z30]),(0,[z0,z1,z2,z789,z4,z30])],[(0,[z0,z1,z2,z56,z4,z30]),(0,[z36,z0,z141,z2,z3,z123]),(0,[z0,z1,z2,z984,z3,z4]),(0,[z0,z1,z2,z3,z130,z30])],[(0,[z0,z1,z2,z3,z4,z985]),(0,[z669,z1,z2,z78,z4,z6]),(0,[z0,z300,z222,z3,z4,z6]),(0,[z0,z1,z2,z3,z7,z161]),(0,[z0,z1,z2,z3,z565,z6]),(0,[z0,z1,z2,z3,z81,z6])],[(0,[z0,z1,z71,z2,z3,z30]),(0,[z0,z1,z2,z3,z6,z858]),(0,[z400,z36,z1,z2,z3,z4])],[(0,[z0,z1,z2,z986,z4,z6]),(0,[z0,z1,z2,z987,z4,z6]),(0,[z0,z1,z988,z3,z4,z6]),(0,[z36,z826,z0,z1,z2,z3])]],
   [[(0,[z0,z1,z989,z2,z3,z4]),(0,[z72,z0,z1,z2,z140,z30]),(0,[z0,z1,z800,z2,z3,z30])],[(0,[z0,z1,z990,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z991]),(0,[z0,z1,z50,z3,z4,z110]),(0,[z0,z189,z2,z3,z4,z8]),(0,[z84,z1,z256,z3,z4,z38]),(0,[z0,z1,z2,z3,z307,z6])],[(0,[z0,z992,z2,z3,z4,z6]),(0,[z0,z1,z2,z687,z3,z30]),(0,[z1,z2,z3,z4,z6,z858]),(0,[z36,z0,z32,z2,z33,z4]),(0,[z0,z1,z3,z760,z4,z6]),(0,[z0,z1,z2,z3,z993,z6])],[(0,[z0,z1,z2,z3,z994,z6]),(0,[z586,z1,z2,z143,z4,z6]),(0,[z0,z995,z2,z3,z4,z6]),(0,[z0,z1,z996,z3,z4,z6]),(0,[z0,z2,z772,z43,z4,z6]),(0,[z0,z1,z2,z3,z420,z6]),(0,[z0,z1,z703,z2,z3,z30])],[(0,[z0,z623,z1,z2,z3,z30]),(0,[z0,z2,z3,z772,z4,z6]),(0,[z36,z0,z1,z2,z3,z341]),(0,[z396,z0,z1,z3,z217,z4])],[(0,[z286,z1,z2,z3,z4,z20]),(0,[z393,z0,z1,z2,z3,z30]),(0,[z0,z1,z2,z3,z163,z30]),(0,[z36,z0,z1,z9,z3,z58]),(0,[z0,z1,z2,z810,z3,z10]),(0,[z0,z1,z2,z795,z4,z93])],[(0,[z36,z0,z1,z251,z3,z4]),(0,[z0,z109,z2,z3,z123,z30]),(0,[z0,z1,z2,z3,z319,z30]),(0,[z0,z1,z105,z3,z4,z30]),(0,[z72,z300,z2,z3,z6,z106]),(0,[z526,z1,z2,z3,z4,z38]),(0,[z0,z1,z2,z3,z997,z6]),(0,[z532,z0,z1,z2,z3,z30])],[(0,[z0,z1,z2,z3,z4,z134])]],
   [[(0,[z0,z1,z2,z3,z998,z6]),(0,[z0,z1,z2,z810,z3,z4]),(0,[z100,z0,z1,z2,z22,z3])],[(0,[z0,z1,z211,z3,z5,z6]),(0,[z0,z1,z2,z3,z4,z999]),(0,[z0,z1,z2,z3,z4,z1000]),(0,[z0,z300,z2,z259,z4,z6]),(0,[z1001,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z57,z23,z4]),(0,[z100,z0,z1,z2,z3,z308]),(0,[z0,z1,z2,z819,z4,z30])],[(0,[z151,z1,z157,z353,z4,z6]),(0,[z0,z1,z2,z3,z1002,z4]),(0,[z1003,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z767,z4,z6])],[(0,[z1,z2,z3,z4,z903,z20]),(0,[z0,z1,z50,z3,z378,z4]),(0,[z0,z1,z50,z381,z3,z4]),(0,[z69,z0,z1,z2,z389,z4])],[(0,[z0,z1,z2,z88,z4,z243]),(0,[z0,z1,z1004,z3,z4,z6]),(1,[z1,z138,z143,z4,z6]),(0,[z72,z0,z1,z2,z3,z30])],[(0,[z0,z1,z1005,z3,z4,z6]),(0,[z0,z1,z2,z3,z1006,z6]),(0,[z0,z1,z138,z3,z4,z30]),(0,[z1,z2,z138,z143,z4,z6]),(0,[z0,z1,z2,z1007,z4,z6]),(0,[z0,z1,z1008,z3,z4,z6]),(0,[z0,z1009,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1010]),(0,[z0,z1,z2,z459,z3,z30]),(0,[z334,z0,z1,z451,z3,z4])],[(0,[z0,z1,z2,z1011,z4,z6]),(0,[z29,z1,z2,z143,z4,z30]),(0,[z0,z1,z2,z3,z1012,z6]),(0,[z1013,z0,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z230,z5,z6]),(0,[z1014,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z181,z4,z6]),(0,[z19,z1,z2,z3,z4,z903]),(0,[z1,z2,z3,z4,z38,z903]),(0,[z0,z1,z2,z3,z1015,z4]),(0,[z0,z1,z2,z3,z1016,z4]),(0,[z1017,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z3,z81])],[(0,[z412,z1,z2,z3,z4,z6]),(0,[z393,z0,z1,z2,z3,z161])],[(0,[z0,z1,z1018,z3,z4,z6]),(0,[z61,z0,z890,z3,z4,z6])],[(0,[z0,z1,z222,z3,z4,z134])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z107,z3,z4,z6]),(0,[z72,z73,z1,z2,z3,z30]),(0,[z0,z1,z1019,z3,z4,z6]),(0,[z0,z281,z2,z3,z4,z439])],[(0,[z1020,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z1021,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1022]),(0,[z250,z1,z2,z78,z4,z6]),(0,[z1023,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z908,z4,z6]),(0,[z1024,z0,z1,z2,z3,z4])],[(0,[z0,z1,z1025,z3,z4,z6]),(0,[z0,z1026,z1,z2,z3,z6]),(0,[z0,z1027,z2,z3,z4,z6]),(0,[z136,z1,z2,z143,z4,z6]),(1,[z0,z1,z283,z3,z30]),(0,[z1028,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1029]),(0,[z0,z1,z2,z3,z223,z30]),(0,[z526,z0,z1,z2,z3,z30])]],
   [[(0,[z36,z0,z1,z256,z3,z4]),(0,[z0,z1,z3,z736,z4,z6]),(0,[z1030,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z22,z3,z4]),(0,[z0,z1,z1031,z3,z4,z6])],[(1,[z1,z2,z3,z6,z858]),(0,[z0,z1,z2,z1032,z3,z4]),(0,[z0,z1,z2,z882,z3,z6])],[(0,[z0,z1,z2,z3,z161,z30]),(0,[z0,z1,z2,z3,z4,z387])],[(0,[z0,z1,z1033,z3,z4,z6]),(0,[z0,z1,z157,z224,z4,z6]),(0,[z0,z1,z807,z3,z4,z6])],[(0,[z19,z247,z1,z2,z3,z4])],[(0,[z0,z1,z2,z1034,z4,z6]),(0,[z0,z144,z1,z2,z3,z30]),(0,[z0,z1,z2,z3,z4,z1035]),(0,[z0,z300,z2,z3,z6,z106]),(0,[z0,z1,z283,z3,z6,z30]),(0,[z0,z1,z2,z3,z201,z30]),(0,[z0,z1,z2,z1036,z3,z4]),(0,[z0,z2,z3,z122,z123,z30])],[(0,[z0,z1,z2,z1037,z4,z6]),(0,[z29,z36,z1,z2,z143,z4]),(0,[z0,z1,z2,z143,z290,z4]),(0,[z0,z1,z2,z361,z57,z93]),(1,[z0,z1,z2,z795,z4])],[(0,[z0,z1,z2,z1038,z4,z6]),(0,[z0,z1039,z2,z3,z4,z6]),(0,[z0,z1,z2,z259,z4,z134]),(0,[z0,z1,z2,z3,z244,z30])]],
   [[(0,[z212,z742,z2,z3,z4,z6]),(0,[z0,z1,z222,z3,z4,z6]),(0,[z0,z1,z2,z1040,z4,z6])],[(0,[z0,z1,z211,z3,z4,z30]),(0,[z0,z1,z707,z3,z4,z6]),(0,[z0,z1,z1041,z3,z4,z6]),(0,[z77,z36,z1,z2,z78,z4]),(0,[z36,z0,z300,z2,z3,z4])],[(0,[z0,z1,z1042,z3,z4,z6]),(0,[z72,z0,z1,z2,z259,z30]),(0,[z36,z0,z1,z2,z181,z4]),(0,[z826,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z860,z4,z30])],[(0,[z212,z26,z2,z88,z4,z6]),(0,[z0,z1043,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z698,z30]),(0,[z0,z1,z2,z3,z123,z30]),(0,[z1044,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1045]),(0,[z1046,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z111,z112,z113])],[(0,[z1047,z0,z2,z3,z4,z6]),(0,[z0,z1,z116,z3,z290,z4]),(0,[z0,z164,z1,z2,z3,z30])],[(0,[z0,z1,z2,z3,z4,z243]),(0,[z0,z1,z2,z3,z1048,z6]),(0,[z0,z1,z2,z224,z4,z30]),(0,[z0,z1,z2,z1049,z4,z6]),(0,[z0,z1,z2,z616,z3,z30]),(0,[z0,z539,z2,z3,z122,z6])],[(0,[z0,z1,z2,z3,z4,z1050]),(0,[z0,z1,z2,z3,z94,z30])]],
   [[(0,[z36,z0,z1,z847,z3,z4])],[(0,[z0,z1,z2,z3,z5,z30]),(0,[z0,z1,z1051,z3,z4,z6]),(0,[z0,z1,z2,z3,z214,z30]),(0,[z1052,z0,z1,z2,z3,z6]),(0,[z296,z0,z1,z2,z12,z4]),(0,[z72,z1,z2,z3,z6,z106]),(0,[z36,z0,z1,z2,z56,z4]),(0,[z0,z1,z2,z112,z113,z6])],[(0,[z0,z1,z34,z2,z3,z4]),(0,[z98,z36,z0,z2,z3,z122]),(0,[z0,z1,z2,z3,z4,z428])],[(0,[z0,z239,z2,z3,z4,z30]),(0,[z0,z1,z1053,z3,z4,z6])],[(0,[z0,z1,z1054,z3,z4,z6]),(0,[z0,z1,z2,z259,z4,z6]),(0,[z0,z1,z2,z3,z4,z1055])],[(0,[z0,z300,z2,z3,z6,z30]),(0,[z100,z0,z1,z2,z3,z288]),(0,[z0,z1,z2,z3,z39,z30])],[(0,[z0,z1,z2,z1056,z4,z6]),(0,[z0,z1,z2,z595,z3,z30])],[(0,[z0,z1,z157,z3,z290,z4]),(0,[z165,z0,z2,z43,z4,z6]),(0,[z0,z1,z2,z3,z1057,z4]),(0,[z0,z1,z2,z3,z596,z30]),(0,[z0,z1,z2,z3,z52,z30])]],
   [[(0,[z0,z1,z2,z3,z123,z330]),(0,[z0,z1,z256,z3,z4,z30])],[(0,[z0,z1058,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1059,z6])],[(0,[z0,z1,z2,z3,z4,z70]),(0,[z0,z1,z2,z3,z1060,z6]),(0,[z412,z1,z2,z75,z4,z6]),(0,[z0,z1,z2,z440,z113,z30])],[(0,[z0,z1,z2,z3,z64,z30]),(0,[z170,z0,z1,z2,z401,z4])],[(0,[z0,z1,z251,z3,z5,z6]),(0,[z0,z1,z2,z3,z194,z30]),(0,[z513,z36,z0,z1,z2,z3]),(0,[z0,z1,z2,z3,z311,z30]),(0,[z0,z1,z800,z2,z3,z4]),(0,[z0,z1,z2,z3,z268,z30]),(0,[z74,z0,z1,z736,z4,z6]),(0,[z74,z0,z1,z75,z4,z30]),(0,[z0,z1,z2,z57,z81,z93])],[(0,[z44,z0,z1,z3,z319,z6]),(0,[z72,z1,z222,z3,z6,z106]),(0,[z0,z1,z1061,z3,z4,z6]),(0,[z0,z141,z2,z3,z175,z123]),(0,[z0,z1,z2,z3,z514,z30])],[(1,[z1,z157,z224,z4,z6]),(0,[z1,z2,z783,z143,z4,z6]),(0,[z326,z0,z1,z2,z3,z4])],[(0,[z36,z0,z1,z2,z3,z180]),(0,[z0,z1,z2,z3,z1062,z6]),(0,[z36,z0,z1,z2,z353,z4]),(0,[z1063,z0,z1,z2,z3,z4]),(0,[z1,z2,z3,z783,z4,z6]),(0,[z0,z32,z2,z33,z4,z30]),(0,[z0,z1,z2,z3,z87,z30])]],
   [[(0,[z723,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z1064,z6]),(0,[z400,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1065]),(0,[z0,z1,z2,z1066,z3,z6]),(0,[z0,z1,z222,z259,z4,z6]),(0,[z0,z1,z2,z3,z453,z30]),(0,[z0,z1,z2,z57,z127,z4]),(0,[z0,z1,z2,z893,z4,z30])],[(0,[z0,z1,z2,z3,z5,z924]),(0,[z0,z1,z2,z3,z97,z30]),(0,[z0,z1,z2,z3,z1067,z4]),(0,[z323,z0,z1,z2,z3,z30]),(0,[z36,z0,z1,z2,z3,z565]),(0,[z0,z1,z2,z114,z3,z241])],[(0,[z77,z1,z2,z78,z4,z6]),(0,[z0,z1,z863,z3,z4,z6]),(0,[z0,z1068,z2,z3,z4,z6])],[],[(1,[z1,z707,z3,z4,z6]),(0,[z0,z1,z1069,z2,z3,z6]),(0,[z0,z1,z2,z3,z1070,z6])],[(0,[z0,z1,z2,z88,z4,z6]),(0,[z212,z26,z2,z3,z4,z6]),(0,[z1,z2,z707,z3,z4,z6]),(0,[z1,z138,z3,z143,z4,z6])],[(0,[z0,z1,z2,z3,z7,z201]),(0,[z1071,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z75,z761])],[(0,[z0,z1,z2,z57,z4,z619]),(0,[z0,z1,z2,z3,z259,z30])]],
   [[(0,[z165,z0,z2,z772,z4,z6]),(0,[z0,z1,z2,z3,z1072,z4])],[(0,[z0,z1,z2,z1073,z4,z6]),(0,[z0,z1,z2,z687,z113,z6]),(0,[z0,z1,z2,z3,z1074,z6]),(0,[z0,z160,z2,z3,z161,z8]),(0,[z0,z1,z2,z3,z1075,z4]),(0,[z0,z1,z2,z203,z3,z30])],[(0,[z0,z1,z1076,z3,z4,z6]),(0,[z166,z0,z1,z2,z3,z30])],[(0,[z0,z1077,z2,z3,z4,z6]),(0,[z1078,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z1079,z4,z6]),(0,[z0,z1,z9,z3,z729,z6])],[(0,[z0,z1,z2,z56,z4,z6]),(0,[z0,z1,z107,z56,z4,z6]),(0,[z0,z2,z3,z122,z741,z6]),(0,[z0,z1,z155,z2,z3,z30]),(0,[z399,z0,z155,z2,z3,z4])],[(0,[z0,z1080,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z148,z30])],[(0,[z1,z742,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1081,z6]),(0,[z0,z1,z2,z114,z113,z30]),(0,[z0,z1,z2,z3,z65,z30])],[(0,[z0,z1,z2,z3,z1082,z6]),(0,[z0,z1,z1083,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z747]),(0,[z1084,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z290,z761]),(1,[z0,z1,z3,z744,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z1085]),(0,[z0,z1,z1086,z2,z3,z4])],[(0,[z0,z2,z3,z1087,z4,z6]),(0,[z0,z1,z2,z3,z1088,z4]),(0,[z0,z1,z2,z772,z4,z6])],[(0,[z0,z1,z2,z3,z359,z30]),(0,[z0,z1,z1089,z3,z4,z6]),(0,[z0,z1,z2,z3,z741,z6]),(0,[z44,z0,z1,z3,z10,z30]),(0,[z0,z1,z2,z3,z127,z30])],[(0,[z0,z1,z211,z230,z4,z6]),(0,[z0,z1,z2,z1090,z4,z6]),(0,[z0,z1,z2,z3,z744,z4]),(0,[z0,z1,z2,z57,z4,z93])],[(0,[z0,z1,z251,z3,z4,z30]),(0,[z1091,z0,z1,z2,z3,z4]),(0,[z0,z1,z50,z3,z744,z4])],[(0,[z73,z0,z1,z2,z3,z30])],[(0,[z0,z1,z2,z1092,z3,z4]),(0,[z0,z1,z105,z3,z4,z6]),(0,[z1,z157,z143,z75,z4,z6]),(0,[z0,z1,z2,z3,z4,z1093]),(0,[z0,z1,z2,z3,z4,z1094]),(0,[z0,z281,z2,z3,z123,z6])],[(0,[z0,z1,z2,z3,z1095,z6]),(0,[z212,z26,z2,z3,z4,z243]),(0,[z0,z1,z116,z3,z58,z30]),(0,[z0,z1,z283,z3,z4,z288]),(0,[z0,z1,z2,z3,z567,z30]),(0,[z0,z1,z2,z114,z3,z30])]],
   [[(0,[z36,z73,z1,z2,z3,z117]),(0,[z1096,z0,z1,z2,z3,z4]),(0,[z0,z1,z1097,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1098]),(1,[z0,z1,z3,z729,z6]),(0,[z0,z1,z2,z745,z4,z6])],[(0,[z0,z1,z2,z1099,z4,z6]),(0,[z0,z1,z2,z3,z1100,z6]),(0,[z898,z1,z2,z3,z4,z6]),(0,[z0,z1,z253,z3,z4,z51])],[(0,[z0,z1,z138,z78,z4,z6]),(0,[z0,z1,z300,z2,z3,z30]),(0,[z1,z2,z3,z4,z903,z6]),(0,[z1101,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z355,z3,z30]),(0,[z0,z1,z829,z3,z4,z30])],[(0,[z0,z1,z2,z3,z1102,z6]),(0,[z666,z0,z1,z2,z3,z30]),(0,[z373,z1,z2,z3,z117,z6]),(0,[z74,z0,z1,z290,z75,z4]),(0,[z11,z0,z1,z2,z440,z4])],[(0,[z0,z1,z1103,z2,z3,z4]),(0,[z631,z1,z2,z143,z4,z6]),(0,[z29,z1,z2,z783,z4,z6]),(1,[z0,z1,z2,z259,z30]),(0,[z0,z1,z2,z3,z4,z1104]),(0,[z0,z141,z2,z3,z123,z258]),(0,[z0,z160,z2,z3,z773,z4]),(0,[z0,z1105,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z729,z6])],[(0,[z167,z0,z1,z3,z129,z4]),(0,[z432,z1,z2,z143,z4,z6]),(0,[z19,z1,z2,z3,z4,z20]),(0,[z0,z1,z2,z1106,z4,z6]),(0,[z0,z1,z2,z3,z263,z30]),(0,[z0,z1,z2,z3,z4,z1107]),(0,[z0,z1,z3,z10,z58,z30]),(0,[z0,z1,z2,z3,z474,z30])],[(0,[z0,z1,z2,z1108,z4,z6]),(0,[z0,z1,z283,z3,z4,z30]),(0,[z84,z1,z2,z3,z4,z903]),(0,[z1109,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z639,z30]),(0,[z0,z1,z2,z3,z776,z4]),(0,[z826,z0,z1,z2,z3,z65])],[(0,[z1110,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z122,z258]),(0,[z0,z1,z253,z3,z4,z215])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 526) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 526).take 527) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1053).take 131) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1184)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [526, 527, 131] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 109).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 109).take 106).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 215).take 41).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [109, 106, 41] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

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

end PEqualNP.Outside.L_meta_43984

theorem PEqualNP.Outside.L_meta_43984 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813544 * 2 ^ 32 + 4276799624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813544 * 2 ^ 32 + 4276799624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_43984.solve