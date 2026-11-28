import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38935

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
  Nat.testBit (4276809440 * 2 ^ 32 + 4276150496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0003661c461c6316#64 ++ 0x40003661c461c631#64 ++ 0xb04fee3cc63ce73f#64 ++ 0xab04fee3cc63ce73#64 : BitVec 256),
   (0x009706c506c52944#64 ++ 0x8009706c506c5294#64 ++ 0xd1b717c707c739cf#64 ++ 0x7d1b717c707c739c#64 : BitVec 256),
   (0x26281802980294a9#64 ++ 0x026281802980294a#64 ++ 0x6e381807f807fffe#64 ++ 0xf6e381807f807fff#64 : BitVec 256),
   (0x1b401b682b683e0e#64 ++ 0x01b401b682b683e0#64 ++ 0xffc01ff83ff83e0d#64 ++ 0xfffc01ff83ff83e0#64 : BitVec 256),
   (0x4dfda00035b7c000#64 ++ 0x04dfda00035b7c00#64 ++ 0x7fffe0003fffc00b#64 ++ 0xe7fffe0003fffc00#64 : BitVec 256),
   (0x8ffeddb7c0000000#64 ++ 0x08ffeddb7c000000#64 ++ 0x8fffffffc0000007#64 ++ 0xf8fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [7, 2]⟩, ⟨.and, [6, 3]⟩, ⟨.or, [9, 8]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [6, 11]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [10, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xb04fee3cc63ce73f 0xab04fee3cc63ce73

def z1 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xd1b717c707c739cf 0x7d1b717c707c739c

def z2 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xffc01ff83ff83e0d 0xfffc01ff83ff83e0

def z3 : W := mkw 0x1b431f6c2f6c3f0e 0x01b431f6c2f6c3f0 0xffc71ffc3ffc3f0f 0xfffc71ffc3ffc3f0

def z4 : W := mkw 0x26281802980294a9 0x026281802980294a 0x6e381807f807fffe 0xf6e381807f807fff

def z5 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7fffe0003fffc00b 0xe7fffe0003fffc00

def z6 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8fffffffc0000007 0xf8fffffffc000000

def z7 : W := mkw 0x8ffc99a380000000 0x08ffc99a38000000 0x8ff01ffb00000005 0xf8ff01ffb0000000

def z8 : W := mkw 0x0dfc800000000000 0x00dfc80000000000 0x0fffe00000000003 0xe0fffe0000000000

def z9 : W := mkw 0x100002482b683e0e 0x0100002482b683e0 0x700000003ff83e08 0x0700000003ff83e0

def z10 : W := mkw 0x84bfe69fc61c6316 0x484bfe69fc61c631 0xb07fee3fc63ce73f 0xab07fee3fc63ce73

def z11 : W := mkw 0x22001802880014a9 0x022001802880014a 0x00001807c0003ff4 0x100001807c0003ff

def z12 : W := mkw 0x8dfec5b540000000 0x08dfec5b54000000 0x8fffe7f800000003 0xe8fffe7f80000000

def z13 : W := mkw 0x0000000000000000 0x0000000000000000 0x40301007000739ce 0x740301007000739c

def z14 : W := mkw 0x009400c100c10840 0x8009400c100c1084 0x41b011c301c318c0 0x541b011c301c318c

def z15 : W := mkw 0x200122081e1ef7bf 0x4200122081e1ef7b 0x700000003e3ffff8 0x0700000003e3ffff

def z16 : W := mkw 0x0002441440000000 0x0000244144000000 0x804fee3cc0000007 0xa804fee3cc000000

def z17 : W := mkw 0x8fffffbfc61c6316 0x48fffffbfc61c631 0xbfffffffc63ce73f 0xfbfffffffc63ce73

def z18 : W := mkw 0xaffeddb7d80294a9 0x0affeddb7d80294a 0xeffffffff807ffff 0xfeffffffff807fff

def z19 : W := mkw 0x0b40192000000000 0x00b4019200000000 0x8fc01ff800000005 0xf8fc01ff80000000

def z20 : W := mkw 0x89d6c5b540000000 0x089d6c5b54000000 0x81c7e7f800000001 0x081c7e7f80000000

def z21 : W := mkw 0x0428000010028000 0x0042800001002800 0x6e3800003807c00a 0xe6e3800003807c00

def z22 : W := mkw 0x8ffeddb7d0028000 0x08ffeddb7d002800 0xeffffffff807c00f 0xfeffffffff807c00

def z23 : W := mkw 0x8f6add36c0000000 0x08f6add36c000000 0x8e4fee3cc0000007 0xa8e4fee3cc000000

def z24 : W := mkw 0x0000020802082206 0x0000002080208220 0xb0400e380638260d 0xab0400e380638260

def z25 : W := mkw 0x009704c504c50940 0x8009704c504c5094 0x41b711c701c719c2 0x541b711c701c719c

def z26 : W := mkw 0x59d5a36827fd6a06 0x059d5a36827fd6a0 0x91c7e7f807f80001 0x091c7e7f807f8000

def z27 : W := mkw 0x0002461c42082206 0x00002461c4208220 0xb04fee3cc638260f 0xab04fee3cc638260

def z28 : W := mkw 0x0003641444144110 0x4000364144414411 0x0007e00000000000 0x00007e0000000000

def z29 : W := mkw 0x0b40192000000000 0x00b4019200000000 0x0e40083800000000 0x80e4008380000000

def z30 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x3fcfe0003ff8c001 0x83fcfe0003ff8c00

def z31 : W := mkw 0x0940000021200000 0x0094000002120000 0x7fc000003ff80009 0xe7fc000003ff8000

def z32 : W := mkw 0x44bda0001497c000 0x044bda0001497c00 0x003fe0000007c002 0x0003fe0000007c00

def z33 : W := mkw 0x84bec497c0000000 0x084bec497c000000 0x003fe007c0000002 0x0003fe007c000000

def z34 : W := mkw 0x82025db7c0000000 0x082025db7c000000 0x80001fffc0000004 0x180001fffc000000

def z35 : W := mkw 0x49d5a00025b54000 0x049d5a00025b5400 0x11c7e00007f80001 0x011c7e00007f8000

def z36 : W := mkw 0x0dff86c506c52944 0x80dff86c506c5294 0xdffff7c707c739cf 0xfdffff7c707c739c

def z37 : W := mkw 0x8fffdff7c6c52944 0x88fffdff7c6c5294 0xdfffffffc7c739cf 0xfdfffffffc7c739c

def z38 : W := mkw 0x84bec497c0000000 0x084bec497c000000 0x807fee3fc0000007 0xa807fee3fc000000

def z39 : W := mkw 0x0000000000000000 0x0000000000000000 0x20080804c004e73e 0xa20080804c004e73

def z40 : W := mkw 0x26281802980294a9 0x026281802980294a 0x4e301003380318c0 0x54e301003380318c

def z41 : W := mkw 0x262b7e1ede1ef7bf 0x4262b7e1ede1ef7b 0xfe7ffe3ffe3fffff 0xffe7ffe3ffe3ffff

def z42 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7ffff0073ffff9cf 0xf7ffff0073ffff9c

def z43 : W := mkw 0xbffedffffb6abeaf 0x0bffedffffb6abea 0xffffffffffffffff 0xffffffffffffffff

def z44 : W := mkw 0x8bd6ddb7c0000000 0x08bd6ddb7c000000 0x81c7ffffc0000005 0x181c7ffffc000000

def z45 : W := mkw 0xafffffbfde1ef7bf 0x4afffffbfde1ef7b 0xfffffffffe3fffff 0xffffffffffe3ffff

def z46 : W := mkw 0x100002482b683e0e 0x0100002482b683e0 0xf18017c03ff83e0d 0x7f18017c03ff83e0

def z47 : W := mkw 0x0097048504850140 0x8009704850485014 0x40371007000739ce 0x740371007000739c

def z48 : W := mkw 0x12001b680a483e0e 0x012001b680a483e0 0x80001ff800003e04 0x180001ff800003e0

def z49 : W := mkw 0x409726c537f7e944 0x8409726c537f7e94 0xf1b717c73ffff9cf 0x7f1b717c73ffff9c

def z50 : W := mkw 0x4000000031a38000 0x04000000031a3800 0x4000000039c30000 0x04000000039c3000

def z51 : W := mkw 0x1b437f3c6f3c771e 0x41b437f3c6f3c771 0xbe4fee3cfe3ce73f 0xabe4fee3cfe3ce73

def z52 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xfff01fff3fff3fcf 0xffff01fff3fff3fc

def z53 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xbfc00ff83ff80601 0x8bfc00ff83ff8060

def z54 : W := mkw 0x0200180008001408 0x0020018000800140 0x6e00180038003e0c 0xf6e00180038003e0

def z55 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z56 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000040004210e 0x2000000040004210

def z57 : W := mkw 0x0002461c42082316 0x40002461c4208231 0x80000e3cc0002734 0x080000e3cc000273

def z58 : W := mkw 0x49d5a00025b54000 0x049d5a00025b5400 0x51f7e00007ff000b 0x651f7e00007ff000

def z59 : W := mkw 0x009766dd46dd6b56 0xc009766dd46dd6b5 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z60 : W := mkw 0x26bc18c398c39ce9 0x826bc18c398c39ce 0x6fb819c7f9c7fffe 0xf6fb819c7f9c7fff

def z61 : W := mkw 0x1bd71fed2fed3f4e 0x81bd71fed2fed3f4 0xfff71fff3fff3fcf 0xffff71fff3fff3fc

def z62 : W := mkw 0x24bf0487948781e1 0x824bf0487948781e 0x003f0007c007c1f2 0x0003f0007c007c1f

def z63 : W := mkw 0x0001024006c52944 0x80001024006c5294 0x5000000007c739c8 0x05000000007c739c

def z64 : W := mkw 0x0002641c40184212 0x40002641c4018421 0xa04fee3cc038c637 0xaa04fee3cc038c63

def z65 : W := mkw 0x9ffedfffeb683e0e 0x09ffedfffeb683e0 0xfffffffffff83e0f 0xffffffffffff83e0

def z66 : W := mkw 0x24280002900280a1 0x024280002900280a 0x00380007c007c1f2 0x000380007c007c1f

def z67 : W := mkw 0xaffeddb7d00280a1 0x0affeddb7d00280a 0x8fffffffc007c1f7 0xf8fffffffc007c1f

def z68 : W := mkw 0x0ffc992000000000 0x00ffc99200000000 0x8ffffff800000007 0xf8ffffff80000000

def z69 : W := mkw 0x0428000000000000 0x0042800000000000 0x0e38000000000002 0xe0e3800000000000

def z70 : W := mkw 0x062a5c16c0000000 0x0062a5c16c000000 0x8e7ffe3fc0000007 0xf8e7ffe3fc000000

def z71 : W := mkw 0x0001200004144000 0x0000120000414400 0x304fe000063cc00b 0xa304fe000063cc00

def z72 : W := mkw 0x009606c502c12944 0x8009606c502c1294 0xc1b017c701c339c4 0x5c1b017c701c339c

def z73 : W := mkw 0x0000000000000000 0x0000000000000000 0x004fe00000000003 0xa004fe0000000000

def z74 : W := mkw 0x5f68bb683b7afe0e 0x05f68bb683b7afe0 0xffc8fff83ff8fe0d 0xfffc8fff83ff8fe0

def z75 : W := mkw 0x26281802900280a1 0x026281802900280a 0x0e381807c007c1f6 0xf0e381807c007c1f

def z76 : W := mkw 0x0001224806dd6b56 0xc0001224806dd6b5 0x7000000007fffff8 0x07000000007fffff

def z77 : W := mkw 0xaffeddb7d80294a9 0x0affeddb7d80294a 0xcffffffff80318c7 0xfcffffffff80318c

def z78 : W := mkw 0x0940000000000000 0x0094000000000000 0x0fc0000000000001 0xe0fc000000000000

def z79 : W := mkw 0x4dfc800031a38000 0x04dfc800031a3800 0x4fb0000039c30000 0x44fb0000039c3000

def z80 : W := mkw 0x4d69a0003536c000 0x04d69a0003536c00 0x3e4fe0003e3cc00b 0xa3e4fe0003e3cc00

def z81 : W := mkw 0x8ffeddb7c8001408 0x08ffeddb7c800140 0xeffffffff8003e0f 0xfeffffffff8003e0

def z82 : W := mkw 0xcffffdb7d497c000 0x0cffffdb7d497c00 0x8fffffffc007c007 0xf8fffffffc007c00

def z83 : W := mkw 0x0097048504850140 0x8009704850485014 0x0007000000000000 0x0000700000000000

def z84 : W := mkw 0x1b4019282928160a 0x01b4019282928160 0x2e40083838380600 0x82e4008383838060

def z85 : W := mkw 0x0428000010028000 0x0042800001002800 0x003800000007c002 0x0003800000007c00

def z86 : W := mkw 0x92025fffca483e0e 0x092025fffca483e0 0x80001fffc0003e04 0x180001fffc0003e0

def z87 : W := mkw 0x0096048500000000 0x0009604850000000 0xc1b717c7000739cf 0x7c1b717c7000739c

def z88 : W := mkw 0xc4bfe497d497c000 0x0c4bfe497d497c00 0x003fe007c007c002 0x0003fe007c007c00

def z89 : W := mkw 0x0000601840184212 0x4000060184018421 0x2048e838c038c630 0x82048e838c038c63

def z90 : W := mkw 0x4001200035b7c000 0x04001200035b7c00 0x700000003fffc008 0x0700000003fffc00

def z91 : W := mkw 0x1b40196029601c08 0x01b40196029601c0 0x7fc011c03ff81809 0xf7fc011c03ff8180

def z92 : W := mkw 0x0002048500000140 0x8000204850000014 0x00000007000001c0 0x000000007000001c

def z93 : W := mkw 0x120019280808160a 0x0120019280808160 0x0000083800000600 0x0000008380000060

def z94 : W := mkw 0x0dfc800021200000 0x00dfc80002120000 0x7fffe0003ff8000b 0xe7fffe0003ff8000

def z95 : W := mkw 0x0b40192021200000 0x00b4019202120000 0xffc01ff83ff8000d 0xfffc01ff83ff8000

def z96 : W := mkw 0xcffffdb7f5b7c000 0x0cffffdb7f5b7c00 0xffffffffffffc00f 0xfffffffffffffc00

def z97 : W := mkw 0x82975ff7c6c52944 0x882975ff7c6c5294 0xd1b71fffc7c739cf 0x7d1b71fffc7c739c

def z98 : W := mkw 0x00012208061c6316 0x400012208061c631 0x30000000063ce738 0x030000000063ce73

def z99 : W := mkw 0x0095000004850000 0x0009500000485000 0x51b7000007c7000b 0x651b7000007c7000

def z100 : W := mkw 0x4d68a0003132c000 0x04d68a0003132c00 0x2e48e0003838c000 0x82e48e0003838c00

def z101 : W := mkw 0x0000000008001408 0x0000000000800140 0x6000000038003e08 0x06000000038003e0

def z102 : W := mkw 0x4ffdb802b5b7c000 0x04ffdb802b5b7c00 0x7ffff807ffffc00f 0xf7ffff807ffffc00

def z103 : W := mkw 0x24280000180294a9 0x024280000180294a 0x6e3800003807fffa 0xe6e3800003807fff

def z104 : W := mkw 0x4dfda0c135f7c840 0x84dfda0c135f7c84 0x7ffff1c33fffd8cb 0xf7ffff1c33fffd8c

def z105 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0x9047e63806380001 0x09047e6380638000

def z106 : W := mkw 0x009766dd46dd6b56 0xc009766dd46dd6b5 0xd1f7f7ff07ff39cf 0x7d1f7f7ff07ff39c

def z107 : W := mkw 0x009746dd46cd2b56 0xc009746dd46cd2b5 0xd1b71fffc7c73fff 0x7d1b71fffc7c73ff

def z108 : W := mkw 0x0001024006c52944 0x80001024006c5294 0x1000000007c00000 0x01000000007c0000

def z109 : W := mkw 0x0628180280000000 0x0062818028000000 0x0e080800c0000000 0x80e080800c000000

def z110 : W := mkw 0x3f681b6abb6abeaf 0x03f681b6abb6abea 0xfff81fffffffffff 0xffff81ffffffffff

def z111 : W := mkw 0x04bf06c516c7a944 0x804bf06c516c7a94 0xffbf17c73fc7f9cf 0xfffbf17c73fc7f9c

def z112 : W := mkw 0x800245b540000000 0x0800245b54000000 0x800007f800000000 0x0800007f80000000

def z113 : W := mkw 0x49d7a6c527f56944 0x849d7a6c527f5694 0xd1f7f7c707ff39cf 0x7d1f7f7c707ff39c

def z114 : W := mkw 0x0000000000000000 0x0000000000000000 0x00080804c0000006 0xa00080804c000000

def z115 : W := mkw 0xcffeddb7f1a38000 0x0cffeddb7f1a3800 0xcffffffff9c30007 0xfcffffffff9c3000

def z116 : W := mkw 0x00012208061c6316 0x400012208061c631 0x304fe000063ce73b 0xa304fe000063ce73

def z117 : W := mkw 0x20000000180294a9 0x020000000180294a 0x600000003807fff8 0x0600000003807fff

def z118 : W := mkw 0x0000000000000000 0x0000000000000000 0x818017c000000005 0x7818017c00000000

def z119 : W := mkw 0x1940036823682a06 0x01940036823682a0 0x91c007f807f80001 0x091c007f807f8000

def z120 : W := mkw 0x000306c506c52944 0x8000306c506c5294 0xd00017c707c739cc 0x1d00017c707c739c

def z121 : W := mkw 0x26281802980294a9 0x026281802980294a 0x00381807c007fff6 0x100381807c007fff

def z122 : W := mkw 0x26281802980294a9 0x026281802980294a 0x2e080800f800c630 0x82e080800f800c63

def z123 : W := mkw 0x009706cd06cd2b46 0x8009706cd06cd2b4 0xf1f71fff07ff3fcf 0xff1f71fff07ff3fc

def z124 : W := mkw 0x0000004000400800 0x0000000400040080 0x418011c001c01800 0x5418011c001c0180

def z125 : W := mkw 0x12971fed0ecd3f4e 0x812971fed0ecd3f4 0xd1b71fff07c73fcf 0x7d1b71fff07c73fc

def z126 : W := mkw 0x6ffdb802bdb7d4a9 0x06ffdb802bdb7d4a 0x7ffff807ffffffff 0xf7ffff807fffffff

def z127 : W := mkw 0x9fffffffef7c7f1e 0x49fffffffef7c7f1 0xfffffffffffcff3f 0xffffffffffffcff3

def z128 : W := mkw 0x8b425db7c0000000 0x08b425db7c000000 0x8fc01fffc0000005 0xf8fc01fffc000000

def z129 : W := mkw 0x0628180290028000 0x0062818029002800 0x6e381807f807c00e 0xf6e381807f807c00

def z130 : W := mkw 0xcfffffbff7bfe316 0x4cfffffbff7bfe31 0xffffffffffffe73f 0xfffffffffffffe73

def z131 : W := mkw 0x000306c506442944 0x8000306c50644294 0x900717c7060439cf 0x3900717c7060439c

def z132 : W := mkw 0x8f68f93ac0184212 0x48f68f93ac018421 0x2e48e838c038c630 0x82e48e838c038c63

def z133 : W := mkw 0x8ffc99a380000000 0x08ffc99a38000000 0x0fb011c300000000 0x50fb011c30000000

def z134 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xf1bf1fc7c7c7ffff 0xff1bf1fc7c7c7fff

def z135 : W := mkw 0x4dffe61c77bfe316 0x44dffe61c77bfe31 0xffffee3cffffe73f 0xeffffee3cffffe73

def z136 : W := mkw 0x4dffa6c537f7e944 0x84dffa6c537f7e94 0xfffff7c73ffff9cf 0xffffff7c73ffff9c

def z137 : W := mkw 0x06bf1ec786c52944 0x806bf1ec786c5294 0xdfbf1fc7c7c739cf 0xfdfbf1fc7c7c739c

def z138 : W := mkw 0x0002441440000000 0x0000244144000000 0xa04fee3cc004e73f 0xaa04fee3cc004e73

def z139 : W := mkw 0x02001a080a08360e 0x002001a080a08360 0xfe401e383e383e0d 0xffe401e383e383e0

def z140 : W := mkw 0x9ffeddf7e9601c08 0x09ffeddf7e9601c0 0xcffffffff9c01807 0xfcffffffff9c0180

def z141 : W := mkw 0x1b425f7c6b683e0e 0x01b425f7c6b683e0 0xffcffffcfff83e0f 0xfffcffffcfff83e0

def z142 : W := mkw 0x009604c500c10840 0x8009604c500c1084 0xc1b717c701c318c7 0x7c1b717c701c318c

def z143 : W := mkw 0x3f68192ab92a96ab 0x03f68192ab92a96a 0x2e480838f838c630 0x82e480838f838c63

def z144 : W := mkw 0x0000200800184212 0x4000020080018421 0x200000000038c630 0x0200000000038c63

def z145 : W := mkw 0x1b437f7c6f7c7f1e 0x41b437f7c6f7c7f1 0xffcffffcfffcff3f 0xfffcffffcfffcff3

def z146 : W := mkw 0x0003060c060c2306 0x00003060c060c230 0xb0470e3c063c270f 0xab0470e3c063c270

def z147 : W := mkw 0x4001224037f7e944 0x84001224037f7e94 0x700000003ffff9c8 0x0700000003ffff9c

def z148 : W := mkw 0x49d7e61c67bd6316 0x449d7e61c67bd631 0xb1cfee3cc7fce73f 0xab1cfee3cc7fce73

def z149 : W := mkw 0x0094000000810000 0x0009400000081000 0x41b0000001c30000 0x441b0000001c3000

def z150 : W := mkw 0x7ffdbb6abffffeaf 0x07ffdbb6abffffea 0xffffffffffffffff 0xffffffffffffffff

def z151 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x2e7fe000383fc002 0x82e7fe000383fc00

def z152 : W := mkw 0x6f68b802b932d4a9 0x06f68b802b932d4a 0x6e78f807f83ffffe 0xf6e78f807f83ffff

def z153 : W := mkw 0x8ffcd932c0000000 0x08ffcd932c000000 0x0fffe838c0000003 0xe0fffe838c000000

def z154 : W := mkw 0x0003641444144110 0x4000364144414411 0x304fe004c63cc13b 0xa304fe004c63cc13

def z155 : W := mkw 0x89d7c7f546c52944 0x889d7c7f546c5294 0xd1f7f7ff07c739cf 0x7d1f7f7ff07c739c

def z156 : W := mkw 0x0002461c42082316 0x40002461c4208231 0x804fee3cc0002737 0xa804fee3cc000273

def z157 : W := mkw 0x0000000000000000 0x0000000000000000 0x00300007000701c2 0x000300007000701c

def z158 : W := mkw 0x24280002980294a9 0x024280002980294a 0x60380007f807fffa 0x060380007f807fff

def z159 : W := mkw 0x4dffa60437b7e104 0x04dffa60437b7e10 0xffffe6043fffe10f 0xeffffe6043fffe10

def z160 : W := mkw 0x26281802980294a9 0x026281802980294a 0x2e080804f804e73e 0xa2e080804f804e73

def z161 : W := mkw 0x4dfda20837bfe206 0x04dfda20837bfe20 0xffffee383fffe60f 0xeffffee383fffe60

def z162 : W := mkw 0x22001802880014a9 0x022001802880014a 0x00001003000018c0 0x100001003000018c

def z163 : W := mkw 0x0000024002402804 0x0000002400240280 0x5000000007c03808 0x05000000007c0380

def z164 : W := mkw 0x1940036823682a06 0x01940036823682a0 0xd1c017f807f8380d 0x7d1c017f807f8380

def z165 : W := mkw 0x0428000280000000 0x0042800028000000 0x00380007c0000002 0x000380007c000000

def z166 : W := mkw 0x0003641444144110 0x4000364144414411 0x000fe004c004c132 0x0000fe004c004c13

def z167 : W := mkw 0x4dffe41475b7c110 0x44dffe41475b7c11 0x7fffe004ffffc13b 0xe7fffe004ffffc13

def z168 : W := mkw 0x5ffc9b683bebbe0e 0x05ffc9b683bebbe0 0xfff01ff83ffb3e0d 0xffff01ff83ffb3e0

def z169 : W := mkw 0x26281802980294a9 0x026281802980294a 0x2e081807f800fff4 0x92e081807f800fff

def z170 : W := mkw 0x1000004029601c08 0x01000004029601c0 0x4000000039c01800 0x04000000039c0180

def z171 : W := mkw 0x0000024002402804 0x0000002400240280 0xd18017c007c0380d 0x7d18017c007c0380

def z172 : W := mkw 0x24280002900280a1 0x024280002900280a 0x40381007c007f9fe 0x740381007c007f9f

def z173 : W := mkw 0x4941200035b7c000 0x04941200035b7c00 0x7fc000003fffc009 0xe7fc000003fffc00

def z174 : W := mkw 0x0dfc800010028000 0x00dfc80001002800 0x6fffe0003807c00b 0xe6fffe0003807c00

def z175 : W := mkw 0x0000000000000000 0x0000000000000000 0x60381807c007fffe 0xf60381807c007fff

def z176 : W := mkw 0x1b407b786b787e1e 0x41b407b786b787e1 0xffc8fff8fff8fe3d 0xfffc8fff8fff8fe3

def z177 : W := mkw 0x86beddb7c0000000 0x086beddb7c000000 0x803fffffc0000006 0x1803fffffc000000

def z178 : W := mkw 0x600120003db7d4a9 0x0600120003db7d4a 0x700000003ffffff8 0x0700000003ffffff

def z179 : W := mkw 0x242b6416d416c1b1 0x4242b6416d416c1b 0x003fe007c007c1f2 0x0003fe007c007c1f

def z180 : W := mkw 0x0002048500000000 0x0000204850000000 0x800017c700000004 0x1800017c70000000

def z181 : W := mkw 0x19d707ed27ed2b46 0x819d707ed27ed2b4 0x91c707f807f80001 0x091c707f807f8000

def z182 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0x7e4008383ff83e08 0x87e4008383ff83e0

def z183 : W := mkw 0x0b401b6002402804 0x00b401b600240280 0xdfc01ff807c0380d 0xfdfc01ff807c0380

def z184 : W := mkw 0x00012208061c6206 0x000012208061c620 0xb04fee38063ce60f 0xab04fee38063ce60

def z185 : W := mkw 0x009606c502402804 0x0009606c50240280 0xd1b717c707c0380f 0x7d1b717c707c0380

def z186 : W := mkw 0x84bfc497c4850140 0x884bfc497c485014 0x003fe007c00701c2 0x0003fe007c00701c

def z187 : W := mkw 0x500122483ffffe0e 0x0500122483ffffe0 0x700000003ffffe08 0x0700000003ffffe0

def z188 : W := mkw 0x26281802980294a9 0x026281802980294a 0x4e381807f80318c6 0xf4e381807f80318c

def z189 : W := mkw 0x20000000180294a9 0x020000000180294a 0x60080804f807fffe 0xa60080804f807fff

def z190 : W := mkw 0x0dfe848500000000 0x00dfe84850000000 0x8ffff7c700000007 0xf8ffff7c70000000

def z191 : W := mkw 0x1b40196029601c08 0x01b40196029601c0 0x4f8011c039c01800 0x54f8011c039c0180

def z192 : W := mkw 0x0628180280000000 0x0062818028000000 0x0e30100300000000 0x50e3010030000000

def z193 : W := mkw 0x0003641c441c4312 0x40003641c441c431 0x204fe83cc03cc732 0x8204fe83cc03cc73

def z194 : W := mkw 0x262b7e1ede1ef7bf 0x4262b7e1ede1ef7b 0xbe4fee3cfe3ce73f 0xabe4fee3cfe3ce73

def z195 : W := mkw 0x0097669d461c6316 0x40097669d461c631 0xb1ffffffc63ce73f 0xfb1ffffffc63ce73

def z196 : W := mkw 0x4ffdb92035b7c000 0x04ffdb92035b7c00 0xfffffff83fffc00f 0xffffffff83fffc00

def z197 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0x91c01ff807f83e05 0x191c01ff807f83e0

def z198 : W := mkw 0x22001802880014a9 0x022001802880014a 0x40301807c0073ffe 0x740301807c0073ff

def z199 : W := mkw 0x8bd6ddb540000000 0x08bd6ddb54000000 0x8fc7fff800000005 0xf8fc7fff80000000

def z200 : W := mkw 0x8fffdff7c6c52944 0x88fffdff7c6c5294 0x9fffffffc7c00007 0xf9fffffffc7c0000

def z201 : W := mkw 0x0096048500000000 0x0009604850000000 0x81b717c700000007 0x781b717c70000000

def z202 : W := mkw 0x0b425d3440000000 0x00b425d344000000 0x8fcffffcc0000007 0xf8fcffffcc000000

def z203 : W := mkw 0x0003665c465c6b16 0x40003665c465c6b1 0xf1cffffcc7fcff3f 0xff1cffffcc7fcff3

def z204 : W := mkw 0x000000c100400840 0x8000000c10040084 0x000011c3000018c0 0x1000011c3000018c

def z205 : W := mkw 0x262b7c16dc16d5b9 0x4262b7c16dc16d5b 0x6e3ff807f807fffe 0xf6e3ff807f807fff

def z206 : W := mkw 0x0000024002402804 0x0000002400240280 0xd1b017c707c739cf 0x7d1b017c707c739c

def z207 : W := mkw 0x1943677c677c6b16 0x41943677c677c6b1 0xb1cfeffcc7fce73f 0xab1cfeffcc7fce73

def z208 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xae401ff838383e04 0x9ae401ff838383e0

def z209 : W := mkw 0x6f68b802b932d4a9 0x06f68b802b932d4a 0x2e48e800f838c630 0x82e48e800f838c63

def z210 : W := mkw 0x194002482b683e0e 0x0194002482b683e0 0x7fc000003ff83e09 0xe7fc000003ff83e0

def z211 : W := mkw 0xa62a5db7d80294a9 0x0a62a5db7d80294a 0xee381ffff807fffe 0xfee381ffff807fff

def z212 : W := mkw 0x12025f7c4a483f1e 0x412025f7c4a483f1 0x80001ffcc0003f34 0x180001ffcc0003f3

def z213 : W := mkw 0x262a5e1eda0ab7bf 0x4262a5e1eda0ab7b 0xee381e3ff807fffe 0xfee381e3ff807fff

def z214 : W := mkw 0x12001b680a483e0e 0x012001b680a483e0 0xb0401ff806383e0d 0xbb0401ff806383e0

def z215 : W := mkw 0x44bda0001497c000 0x044bda0001497c00 0x51bfe00007c7c00b 0x651bfe00007c7c00

def z216 : W := mkw 0x8f68d932c0000000 0x08f68d932c000000 0x0e48e838c0000000 0x80e48e838c000000

def z217 : W := mkw 0x89d7c7f546c52944 0x889d7c7f546c5294 0x91c7e7f807c00001 0x091c7e7f807c0000

def z218 : W := mkw 0xa4bec497d00280a1 0x0a4bec497d00280a 0x003fe007c007c1f2 0x0003fe007c007c1f

def z219 : W := mkw 0x0094008100810040 0x8009400810081004 0x00300003000300c0 0x000300003000300c

def z220 : W := mkw 0x0097048504850140 0x8009704850485014 0x00370007000701c2 0x000370007000701c

def z221 : W := mkw 0x4dffa6c537f7e944 0x84dffa6c537f7e94 0xffffe7c03fffc00b 0xeffffe7c03fffc00

def z222 : W := mkw 0x8f6addb7c0000000 0x08f6addb7c000000 0x8e48ffffc0000004 0x98e48ffffc000000

def z223 : W := mkw 0x9f68db7aeb683e0e 0x09f68db7aeb683e0 0xffc8fff8fff83e0d 0xfffc8fff8fff83e0

def z224 : W := mkw 0x8ffeddb7e1200000 0x08ffeddb7e120000 0xfffffffffff8000f 0xffffffffffff8000

def z225 : W := mkw 0x9f68d93ae928160a 0x09f68d93ae928160 0x2e48e838f8380600 0x82e48e838f838060

def z226 : W := mkw 0x0bd61da500000000 0x00bd61da50000000 0x8ff71fff00000007 0xf8ff71fff0000000

def z227 : W := mkw 0x12001b680a483e0e 0x012001b680a483e0 0xd1801ff807c03e0d 0x7d1801ff807c03e0

def z228 : W := mkw 0xcffdb9a3b5b7c000 0x0cffdb9a3b5b7c00 0x7ffff1c33fffc00b 0xf7ffff1c33fffc00

def z229 : W := mkw 0x0001200004144000 0x0000120000414400 0x30000000063cc008 0x030000000063cc00

def z230 : W := mkw 0x262a5c16d80294a9 0x0262a5c16d80294a 0xee7ffe3ff807ffff 0xfee7ffe3ff807fff

def z231 : W := mkw 0x8fff9fe786c52944 0x88fff9fe786c5294 0xdfb717c707c739cf 0x7dfb717c707c739c

def z232 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8fcfeff8c0000001 0x88fcfeff8c000000

def z233 : W := mkw 0x20000002800000a1 0x020000002800000a 0x00000007c00001f0 0x000000007c00001f

def z234 : W := mkw 0x4dffe6dd77ffeb56 0xc4dffe6dd77ffeb5 0xffffffffffffffff 0xffffffffffffffff

def z235 : W := mkw 0x000206c502402944 0x8000206c50240294 0xd18017c707c039cd 0x7d18017c707c039c

def z236 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0x300fe004c63ce73a 0x0300fe004c63ce73

def z237 : W := mkw 0x0628180280000000 0x0062818028000000 0x0e381807c0000006 0xf0e381807c000000

def z238 : W := mkw 0x4dfda24037f7e944 0x84dfda24037f7e94 0x7fffe0003ffff9cb 0xe7fffe0003ffff9c

def z239 : W := mkw 0x5ffdbb683ffffe0e 0x05ffdbb683ffffe0 0xfffffff83ffffe0f 0xffffffff83ffffe0

def z240 : W := mkw 0x2003661c5e1ef7bf 0x42003661c5e1ef7b 0xf04fee3cfe3fffff 0xaf04fee3cfe3ffff

def z241 : W := mkw 0x0000601040104010 0x4000060104010401 0x0008e000c000c030 0x00008e000c000c03

def z242 : W := mkw 0x000206c502402944 0x8000206c50240294 0x800017c7000039c4 0x1800017c7000039c

def z243 : W := mkw 0x8dfec497c0000000 0x08dfec497c000000 0x0fffe007c0000003 0xe0fffe007c000000

def z244 : W := mkw 0x12001b680a483e0e 0x012001b680a483e0 0xee001ff838003e0c 0xfee001ff838003e0

def z245 : W := mkw 0x009402c102c12844 0x8009402c102c1284 0xd1b017c307c338cd 0x7d1b017c307c338c

def z246 : W := mkw 0x0097068506852144 0x8009706850685214 0x90370607060721cf 0x290370607060721c

def z247 : W := mkw 0x0000024002402944 0x8000002400240294 0x00000000000039c0 0x000000000000039c

def z248 : W := mkw 0x49d7e61c67bd6316 0x449d7e61c67bd631 0x91c7e63807f80001 0x091c7e63807f8000

def z249 : W := mkw 0xaffc99a3980294a9 0x0affc99a3980294a 0x6fb819c7f807fffe 0xf6fb819c7f807fff

def z250 : W := mkw 0xaffc99a3980294a9 0x0affc99a3980294a 0x4fb011c3380318c0 0x54fb011c3380318c

def z251 : W := mkw 0x0002441440000000 0x0000244144000000 0x8047e63800000001 0x08047e6380000000

def z252 : W := mkw 0x4001220837bfe316 0x44001220837bfe31 0x700000003fffe738 0x0700000003fffe73

def z253 : W := mkw 0x0003641444144110 0x4000364144414411 0x200fe804c004e73e 0xa200fe804c004e73

def z254 : W := mkw 0x22001802880014a9 0x022001802880014a 0x6e001807f8003ffc 0xf6e001807f8003ff

def z255 : W := mkw 0x04bc800000000000 0x004bc80000000000 0x003fe00000000002 0x0003fe0000000000

def z256 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0x918707c007c00001 0x0918707c007c0000

def z257 : W := mkw 0x0941200025344000 0x0094120002534400 0x7fcfe0003ffcc00b 0xe7fcfe0003ffcc00

def z258 : W := mkw 0x20000000180294a9 0x020000000180294a 0x200000003800c630 0x0200000003800c63

def z259 : W := mkw 0x44bfa6c516d7e944 0x844bfa6c516d7e94 0xd1bff7c707c7f9cf 0x7d1bff7c707c7f9c

def z260 : W := mkw 0x26281802980294a9 0x026281802980294a 0x6e3010033807fff8 0x56e3010033807fff

def z261 : W := mkw 0x26be1c87980294a9 0x026be1c87980294a 0xefbf1fc7f807ffff 0xfefbf1fc7f807fff

def z262 : W := mkw 0x009400c100c10840 0x8009400c100c1084 0x41b011c701c739ce 0x741b011c701c739c

def z263 : W := mkw 0x6dfda002b5b7c0a1 0x06dfda002b5b7c0a 0x7fffe007ffffc1fb 0xe7fffe007ffffc1f

def z264 : W := mkw 0x0000004000c10840 0x80000004000c1084 0x4000000001c318c0 0x04000000001c318c

def z265 : W := mkw 0x0003665c46dd6b56 0xc0003665c46dd6b5 0xf04fee3cc7ffffff 0xaf04fee3cc7fffff

def z266 : W := mkw 0xafffdff7dec7bded 0x8afffdff7dec7bde 0xffffffffffc7ffff 0xfffffffffffc7fff

def z267 : W := mkw 0x20000000100280a1 0x020000000100280a 0x000000000007c1f0 0x0000000000007c1f

def z268 : W := mkw 0x1b40192029201408 0x01b4019202920140 0x0e00000038000000 0x00e0000003800000

def z269 : W := mkw 0x26bf1ec79ec7bded 0x826bf1ec79ec7bde 0xffbf1fc7ffc7ffff 0xfffbf1fc7ffc7fff

def z270 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8ff7f7fb00000001 0x58ff7f7fb0000000

def z271 : W := mkw 0x26281802980294a9 0x026281802980294a 0x6e3810033807d8ca 0xf6e3810033807d8c

def z272 : W := mkw 0xc9d7e5b565b54000 0x0c9d7e5b565b5400 0x91c7e7f807f80001 0x091c7e7f807f8000

def z273 : W := mkw 0x06be1c8780000000 0x006be1c878000000 0x8fbf1fc7c0000007 0xf8fbf1fc7c000000

def z274 : W := mkw 0x4dffa48535b7c000 0x04dffa48535b7c00 0xfffff7c73fffc00f 0xffffff7c73fffc00

def z275 : W := mkw 0x09d4800000000000 0x009d480000000000 0x01c7e00000000001 0x001c7e0000000000

def z276 : W := mkw 0x2ffc9802980294a9 0x02ffc9802980294a 0x6ffff807f807ffff 0xf6ffff807f807fff

def z277 : W := mkw 0x8fffffffc6dd6b56 0xc8fffffffc6dd6b5 0xffffffffc7ffffff 0xfffffffffc7fffff

def z278 : W := mkw 0x0003060406042104 0x0000306040604210 0xd0371607060739cf 0x7d0371607060739c

def z279 : W := mkw 0x49d5a00025b54000 0x049d5a00025b5400 0x31cfe00007fcc00b 0xa31cfe00007fcc00

def z280 : W := mkw 0x26281802980294a9 0x026281802980294a 0x2e380807f807c7f2 0x82e380807f807c7f

def z281 : W := mkw 0xaffeddb7c80014a9 0x0affeddb7c80014a 0x8fffffffc0003ff7 0xf8fffffffc0003ff

def z282 : W := mkw 0x0940012000000000 0x0094001200000000 0x81c007f800000001 0x081c007f80000000

def z283 : W := mkw 0x0002441440000000 0x0000244144000000 0x80000e3cc0000004 0x080000e3cc000000

def z284 : W := mkw 0x19d707ed27ed2b46 0x819d707ed27ed2b4 0xd1f717ff07ff39cf 0x7d1f717ff07ff39c

def z285 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xb047e638063ce739 0x0b047e638063ce73

def z286 : W := mkw 0x009400c100c10840 0x8009400c100c1084 0x018001c001c00000 0x0018001c001c0000

def z287 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xf07ffe3fc63fffff 0xff07ffe3fc63ffff

def z288 : W := mkw 0x82965db7c0000000 0x082965db7c000000 0x81b71fffc0000007 0x781b71fffc000000

def z289 : W := mkw 0x22001800180294a9 0x022001800180294a 0x6e0018003807fffc 0xf6e0018003807fff

def z290 : W := mkw 0x0095200004954000 0x0009520000495400 0x71ffe00007ffc00b 0xe71ffe00007ffc00

def z291 : W := mkw 0x3f6b7f7eff7effbf 0x43f6b7f7eff7effb 0xffffffffffffffff 0xffffffffffffffff

def z292 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xffc81ffcfffcff3f 0xfffc81ffcfffcff3

def z293 : W := mkw 0x1b413b682f7c7f1e 0x41b413b682f7c7f1 0xffc01ff83ffcff3d 0xfffc01ff83ffcff3

def z294 : W := mkw 0x0096048500000000 0x0009604850000000 0x0037000700000002 0x0003700070000000

def z295 : W := mkw 0x8ffffdb7c4144110 0x48ffffdb7c414411 0x8fffffffc004c137 0xf8fffffffc004c13

def z296 : W := mkw 0x8ffeddf7c0c10840 0x88ffeddf7c0c1084 0xcfffffffc1c318c7 0xfcfffffffc1c318c

def z297 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7fffe804ffffe73f 0xe7fffe804ffffe73

def z298 : W := mkw 0x262a1ec79a42bded 0x8262a1ec79a42bde 0xee381fc7f807fffe 0xfee381fc7f807fff

def z299 : W := mkw 0x66bdb8029c97d4a9 0x066bdb8029c97d4a 0x6e3ff807f807fffe 0xf6e3ff807f807fff

def z300 : W := mkw 0x0003040404040100 0x0000304040404010 0x0007000400040102 0x0000700040004010

def z301 : W := mkw 0x0bd71fe506c52944 0x80bd71fe506c5294 0xdff71fff07c739cf 0xfdff71fff07c739c

def z302 : W := mkw 0x24280002900280a1 0x024280002900280a 0x20380807c007e7fe 0xa20380807c007e7f

def z303 : W := mkw 0x84bec497c0000000 0x084bec497c000000 0x81bff7c7c0000007 0x781bff7c7c000000

def z304 : W := mkw 0x82025ff7c2402944 0x882025ff7c240294 0x80001fffc00039c4 0x180001fffc00039c

def z305 : W := mkw 0x8096c49540000000 0x08096c4954000000 0x0007e00000000000 0x00007e0000000000

def z306 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0x9047ee3cc6382735 0x09047ee3cc638273

def z307 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xb04fee38c638c631 0x8b04fee38c638c63

def z308 : W := mkw 0x0097048504850140 0x8009704850485014 0x81b717c7000701c7 0x781b717c7000701c

def z309 : W := mkw 0x0200180008001408 0x0020018000800140 0x4e00100038001800 0x54e0010003800180

def z310 : W := mkw 0x4001200025b54000 0x04001200025b5400 0x1000000007f80000 0x01000000007f8000

def z311 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xb0000e3cc63ce73c 0x0b0000e3cc63ce73

def z312 : W := mkw 0x100122482f7c7f1e 0x4100122482f7c7f1 0x700000003ffcff38 0x0700000003ffcff3

def z313 : W := mkw 0x0dfec41440000000 0x00dfec4144000000 0x8fffee3cc0000007 0xe8fffee3cc000000

def z314 : W := mkw 0x0000000000000000 0x0000000000000000 0x403000000007000a 0x6403000000007000

def z315 : W := mkw 0xa2025db7c80014a9 0x0a2025db7c80014a 0x80001fffc0003ff4 0x180001fffc0003ff

def z316 : W := mkw 0x0094008100000000 0x0009400810000000 0x01b011c300000000 0x501b011c30000000

def z317 : W := mkw 0x0b40192000000000 0x00b4019200000000 0x0f8011c000000000 0x50f8011c00000000

def z318 : W := mkw 0x009726cd06dd6b56 0xc009726cd06dd6b5 0xf1b717c707ffffff 0x7f1b717c707fffff

def z319 : W := mkw 0x09d5000025a50000 0x009d5000025a5000 0x7ff700003fff000b 0xe7ff700003fff000

def z320 : W := mkw 0x8ffcd9b3c0000000 0x08ffcd9b3c000000 0x0ff8f9fbc0000000 0xd0ff8f9fbc000000

def z321 : W := mkw 0x8dfec5b7c0000000 0x08dfec5b7c000000 0x81ffe7ffc0000003 0x081ffe7ffc000000

def z322 : W := mkw 0x1f681b6aab683e0e 0x01f681b6aab683e0 0xfff81ffffff83e0f 0xffff81ffffff83e0

def z323 : W := mkw 0x5b413b683ffffe0e 0x05b413b683ffffe0 0xffc01ff83ffffe0d 0xfffc01ff83ffffe0

def z324 : W := mkw 0x4dff86c537e7a944 0x84dff86c537e7a94 0xdfb717c73fc739cf 0x7dfb717c73fc739c

def z325 : W := mkw 0x8ffedff7c2402804 0x08ffedff7c240280 0xdfffffffc7c0380f 0xfdfffffffc7c0380

def z326 : W := mkw 0x49d7a6c527f56944 0x849d7a6c527f5694 0x91c7e7c007f80001 0x091c7e7c007f8000

def z327 : W := mkw 0x0200180000000000 0x0020018000000000 0x0e00180000000004 0xf0e0018000000000

def z328 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x5ff7e0003ffb0001 0x45ff7e0003ffb000

def z329 : W := mkw 0x0000024002402804 0x0000002400240280 0x800017c000003804 0x1800017c00000380

def z330 : W := mkw 0x8f68d932c0000000 0x08f68d932c000000 0x0e78f83fc0000006 0xf0e78f83fc000000

def z331 : W := mkw 0x0940020823282206 0x0094002082328220 0xffc00e383ff8260d 0xeffc00e383ff8260

def z332 : W := mkw 0x0000020802082206 0x0000002080208220 0xb0480e3cc63ce73f 0xab0480e3cc63ce73

def z333 : W := mkw 0x2f681802b92294a9 0x02f681802b92294a 0x7ff81807ffffffff 0xf7ff81807fffffff

def z334 : W := mkw 0x24280002900280a1 0x024280002900280a 0x6e380007f807c1fa 0xe6e380007f807c1f

def z335 : W := mkw 0x0001200004144110 0x4000120000414411 0x000000000004c130 0x0000000000004c13

def z336 : W := mkw 0x1b437f7c6f7c7f1e 0x41b437f7c6f7c7f1 0xffc7fff83ff83e0d 0xfffc7fff83ff83e0

def z337 : W := mkw 0x44bfe4145497c110 0x444bfe4145497c11 0x003fe004c007c132 0x0003fe004c007c13

def z338 : W := mkw 0x00016018441c4212 0x400016018441c421 0x304fe838c63cc63b 0xa304fe838c63cc63

def z339 : W := mkw 0x26293a0a9e1ef7bf 0x426293a0a9e1ef7b 0x7e381807fe3ffffe 0xf7e381807fe3ffff

def z340 : W := mkw 0x8ffefdbfc0184212 0x48ffefdbfc018421 0xafffffffc038c637 0xfafffffffc038c63

def z341 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0xafffffffc004e73f 0xfafffffffc004e73

def z342 : W := mkw 0x0097068506042104 0x0009706850604210 0x91b717c70604210f 0x791b717c70604210

def z343 : W := mkw 0x0628180280000000 0x0062818028000000 0x2e381807c004e73e 0xf2e381807c004e73

def z344 : W := mkw 0x4dfda00025b54000 0x04dfda00025b5400 0x1fffe00007f80003 0xe1fffe00007f8000

def z345 : W := mkw 0x22001802980294a9 0x022001802980294a 0x60001807f807fffc 0x160001807f807fff

def z346 : W := mkw 0x26281802980294a9 0x026281802980294a 0x0e00000038000000 0x00e0000003800000

def z347 : W := mkw 0x009766d546d56954 0xc009766d546d5695 0xd1bff7c7c7c7f9ff 0x7d1bff7c7c7c7f9f

def z348 : W := mkw 0x24bf06c796c7a9e5 0x824bf06c796c7a9e 0xd1bf17c7c7c7f9ff 0x7d1bf17c7c7c7f9f

def z349 : W := mkw 0x0002461c42082316 0x40002461c4208231 0x8000063800000000 0x0800006380000000

def z350 : W := mkw 0x1f681b683b6abe0e 0x01f681b683b6abe0 0xfff81ff83ffffe0f 0xffff81ff83ffffe0

def z351 : W := mkw 0x44bfa4851497c140 0x844bfa4851497c14 0x003fe0070007c1c2 0x0003fe0070007c1c

def z352 : W := mkw 0x5f68b928393ad60a 0x05f68b928393ad60 0x2e48e8383838c600 0x82e48e8383838c60

def z353 : W := mkw 0x0000601840184212 0x4000060184018421 0x0040e03800380000 0x00040e0380038000

def z354 : W := mkw 0xcf68f932f132c000 0x0cf68f932f132c00 0x2e48e838f838c000 0x82e48e838f838c00

def z355 : W := mkw 0x2628781ad81ad6bb 0x42628781ad81ad6b 0x6e78f83ff83ffffe 0xf6e78f83ff83ffff

def z356 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xdfc017f83ff81801 0x5dfc017f83ff8180

def z357 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0x5037000707c739ca 0x05037000707c739c

def z358 : W := mkw 0x4d68a0003132c000 0x04d68a0003132c00 0x7fc8e0003ff8c009 0xe7fc8e0003ff8c00

def z359 : W := mkw 0x6fffbec7bff7fded 0x86fffbec7bff7fde 0xffffffc7ffffffff 0xfffffffc7fffffff

def z360 : W := mkw 0xcdffe5b575b7c000 0x0cdffe5b575b7c00 0xffffe7f83fffc00b 0xeffffe7f83fffc00

def z361 : W := mkw 0x1bd77ffd6ffd7f5e 0xc1bd77ffd6ffd7f5 0xffffffffffffffff 0xffffffffffffffff

def z362 : W := mkw 0x20000000180294a9 0x020000000180294a 0x40000000380318c0 0x040000000380318c

def z363 : W := mkw 0x22971ec78ec53ded 0x822971ec78ec53de 0xd1b71fc7c7c73fff 0x7d1b71fc7c7c73ff

def z364 : W := mkw 0x009766dd46dd6b56 0xc009766dd46dd6b5 0x91c7e7f807f80001 0x091c7e7f807f8000

def z365 : W := mkw 0x2628781ad81ad6bb 0x42628781ad81ad6b 0x2e48e838f838c630 0x82e48e838f838c63

def z366 : W := mkw 0x042920001416c000 0x0042920001416c00 0x7e7fe0003e3fc00b 0xe7e7fe0003e3fc00

def z367 : W := mkw 0x9fffdfffefed3f4e 0x89fffdfffefed3f4 0xffffffffffff3fcf 0xfffffffffffff3fc

def z368 : W := mkw 0x2f681922980294a9 0x02f681922980294a 0xeff81ffff807ffff 0xfeff81ffff807fff

def z369 : W := mkw 0x0000401840080212 0x4000040184008021 0x00000838c0000630 0x000000838c000063

def z370 : W := mkw 0x6ffdb802bdb7d4a9 0x06ffdb802bdb7d4a 0x7ffff0033fffd8cb 0xf7ffff0033fffd8c

def z371 : W := mkw 0x26281802980294a9 0x026281802980294a 0x4e301807f8033ff4 0x54e301807f8033ff

def z372 : W := mkw 0x009746d546c52944 0x8009746d546c5294 0xd1ffffffc7c739cf 0xfd1ffffffc7c739c

def z373 : W := mkw 0x26281802980294a9 0x026281802980294a 0x6e081800f800fe3c 0xf6e081800f800fe3

def z374 : W := mkw 0x0b40180029201408 0x00b4018002920140 0x7fc018003ff83e0d 0xf7fc018003ff83e0

def z375 : W := mkw 0x4dfd800035a78000 0x04dfd800035a7800 0x5fb700003fc7000b 0x65fb700003fc7000

def z376 : W := mkw 0x1bd41be92be93e4e 0x81bd41be92be93e4 0xfff01ffb3ffb3ecd 0xffff01ffb3ffb3ec

def z377 : W := mkw 0x4dfc800031a38000 0x04dfc800031a3800 0x4fffe00039c30003 0xe4fffe00039c3000

def z378 : W := mkw 0x0d68000031228000 0x00d6800003122800 0x7ff800003fffc00b 0xe7ff800003fffc00

def z379 : W := mkw 0x1b401b680a483e0e 0x01b401b680a483e0 0x8fc01ff800003e05 0xf8fc01ff800003e0

def z380 : W := mkw 0x200102401ec7bded 0x8200102401ec7bde 0x700000003fc7fff8 0x0700000003fc7fff

def z381 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x11ffe00007ffc003 0x011ffe00007ffc00

def z382 : W := mkw 0x1940036823682a06 0x01940036823682a0 0xb1c00ff807f8260d 0xab1c00ff807f8260

def z383 : W := mkw 0x26bf1c879c8795e9 0x826bf1c879c8795e 0x6e3f1807f807fffe 0xf6e3f1807f807fff

def z384 : W := mkw 0x1b4019282928160a 0x01b4019282928160 0x7fc008383ff80609 0xe7fc008383ff8060

def z385 : W := mkw 0x49d5a00025b54000 0x049d5a00025b5400 0x7fc7e0003ff80009 0xe7fc7e0003ff8000

def z386 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0x91b707c707c701c3 0x091b707c707c701c

def z387 : W := mkw 0x262b1e069e06b5ad 0x0262b1e069e06b5a 0xfe3f1e07fe07ffff 0xffe3f1e07fe07fff

def z388 : W := mkw 0x1b401b282b28360e 0x01b401b282b28360 0xbe400e383e38260d 0xabe400e383e38260

def z389 : W := mkw 0x4d6be61c773ee316 0x44d6be61c773ee31 0xbe4fee3cfe3ce73f 0xabe4fee3cfe3ce73

def z390 : W := mkw 0x400120001497c000 0x0400120001497c00 0x000000000007c000 0x0000000000007c00

def z391 : W := mkw 0x1003665c6f7c7f1e 0x41003665c6f7c7f1 0xf04fee3cfffcff3f 0xaf04fee3cfffcff3

def z392 : W := mkw 0x64bda0029497c0a1 0x064bda0029497c0a 0x003fe007c007c1f2 0x0003fe007c007c1f

def z393 : W := mkw 0x6dfda0003db7d4a9 0x06dfda0003db7d4a 0x7fffe0003ffffffb 0xe7fffe0003ffffff

def z394 : W := mkw 0x0002441440000000 0x0000244144000000 0x000fe004c0000002 0x0000fe004c000000

def z395 : W := mkw 0x89d481a100000000 0x089d481a10000000 0x018001c000000000 0x0018001c00000000

def z396 : W := mkw 0x0095024006c52804 0x00095024006c5280 0xd1b717c007c7380f 0x7d1b717c007c7380

def z397 : W := mkw 0x1b40196829681e0a 0x01b40196829681e0 0x6fc019f839f81e00 0xd6fc019f839f81e0

def z398 : W := mkw 0x0096449540000000 0x0009644954000000 0x81ffffffc0000007 0xf81ffffffc000000

def z399 : W := mkw 0x9bd6dffd6b683e0e 0x09bd6dffd6b683e0 0xffc7fff83ff83e0d 0xfffc7fff83ff83e0

def z400 : W := mkw 0x0003060406042104 0x0000306040604210 0x900706040604210f 0x2900706040604210

def z401 : W := mkw 0x8f68992280000000 0x08f6899228000000 0x0e00000000000000 0x00e0000000000000

def z402 : W := mkw 0x84bfe497c4144110 0x484bfe497c414411 0x003fe007c004c132 0x0003fe007c004c13

def z403 : W := mkw 0x400020003132c000 0x0400020003132c00 0x200000003838c000 0x0200000003838c00

def z404 : W := mkw 0x0200180280000000 0x0020018028000000 0x00001807c0000004 0x100001807c000000

def z405 : W := mkw 0x0003060406042104 0x0000306040604210 0x9007060006000001 0x0900706000600000

def z406 : W := mkw 0x4dffe61c77bfe316 0x44dffe61c77bfe31 0xffffe6383fffc00b 0xeffffe6383fffc00

def z407 : W := mkw 0x1b4019282928160a 0x01b4019282928160 0xafc01ff838380605 0xfafc01ff83838060

def z408 : W := mkw 0x0000000000000000 0x0000000000000000 0x6e00000038000008 0xe6e0000003800000

def z409 : W := mkw 0x44bfe61c569fe316 0x444bfe61c569fe31 0xb07fee3cc63fe73f 0xab07fee3cc63fe73

def z410 : W := mkw 0x062b7e1ec61c6316 0x4062b7e1ec61c631 0xbe7ffe3fc63ce73f 0xfbe7ffe3fc63ce73

def z411 : W := mkw 0x26bf1ec79ec7bded 0x826bf1ec79ec7bde 0xdfb717c73fc739cf 0x7dfb717c73fc739c

def z412 : W := mkw 0x6ffc9802b9a394a9 0x06ffc9802b9a394a 0x6fb81807f9c7fffe 0xf6fb81807f9c7fff

def z413 : W := mkw 0x0000000000000000 0x0000000000000000 0x200000000004e738 0x0200000000004e73

def z414 : W := mkw 0x0001200004144000 0x0000120000414400 0x1047e00006380001 0x01047e0000638000

def z415 : W := mkw 0x0dfc800000000000 0x00dfc80000000000 0x0fb0000000000000 0x40fb000000000000

def z416 : W := mkw 0x1bd71fed2fed3f4e 0x81bd71fed2fed3f4 0xffc71ff83ff83e0d 0xfffc71ff83ff83e0

def z417 : W := mkw 0x000366dd465c6b56 0xc000366dd465c6b5 0xb04fffffc63cffff 0xbb04fffffc63cfff

def z418 : W := mkw 0x44bda00035b7c000 0x044bda00035b7c00 0x703fe0003fffc00a 0x0703fe0003fffc00

def z419 : W := mkw 0x0096048500000000 0x0009604850000000 0x818707c000000001 0x0818707c00000000

def z420 : W := mkw 0x0002461c42082316 0x40002461c4208231 0xb0400e3cc638273d 0xab0400e3cc638273

def z421 : W := mkw 0x862a5db7c0000000 0x0862a5db7c000000 0x8e381fffc0000006 0xf8e381fffc000000

def z422 : W := mkw 0x1b401b6823682a06 0x01b401b6823682a0 0x9fc01ff807f80005 0xf9fc01ff807f8000

def z423 : W := mkw 0xaf68d932d80294a9 0x0af68d932d80294a 0x2e48e838f800c630 0x82e48e838f800c63

def z424 : W := mkw 0xcdffe497f5b7c000 0x0cdffe497f5b7c00 0x7fffe007ffffc00b 0xe7fffe007ffffc00

def z425 : W := mkw 0x0003641444144000 0x0000364144414400 0xb04fee3cc63cc00f 0xab04fee3cc63cc00

def z426 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0x7f8011c03ff83e08 0x57f8011c03ff83e0

def z427 : W := mkw 0x0000024002402804 0x0000002400240280 0x918007c007c00001 0x0918007c007c0000

def z428 : W := mkw 0x9ffeddbfe928160a 0x09ffeddbfe928160 0xaffffffff8380607 0xfaffffffff838060

def z429 : W := mkw 0x0dfd800004850000 0x00dfd80000485000 0x5fffe00007c7000b 0xe5fffe00007c7000

def z430 : W := mkw 0x1000024823682a06 0x01000024823682a0 0x1000000007f80000 0x01000000007f8000

def z431 : W := mkw 0x0000200000104000 0x0000020000010400 0x2048e0000038c000 0x82048e0000038c00

def z432 : W := mkw 0x12001a482b683e0e 0x012001a482b683e0 0x7e0018003ff83e0c 0xf7e0018003ff83e0

def z433 : W := mkw 0x0097048504850000 0x0009704850485000 0xd1b717c707c7000f 0x7d1b717c707c7000

def z434 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000804c0002734 0x000000804c000273

def z435 : W := mkw 0x8ffedfbfc2082316 0x48ffedfbfc208231 0x8fffffffc0002737 0xf8fffffffc000273

def z436 : W := mkw 0x5ffdb9603df7dc08 0x05ffdb9603df7dc0 0x7ffff1c03fffd80b 0xf7ffff1c03fffd80

def z437 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xd1b717c307c318c1 0x5d1b717c307c318c

def z438 : W := mkw 0x8ffffdb7c4144000 0x08ffffdb7c414400 0xbfffffffc63cc00f 0xfbfffffffc63cc00

def z439 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0xcfffffffc00739cf 0xfcfffffffc00739c

def z440 : W := mkw 0x4940a00021304000 0x04940a0002130400 0x0040e00000380000 0x00040e0000038000

def z441 : W := mkw 0xcffffdb7e5b54000 0x0cffffdb7e5b5400 0x9fffffffc7f80007 0xf9fffffffc7f8000

def z442 : W := mkw 0x009500c104c50840 0x8009500c104c5084 0x51b711c307c718cb 0x751b711c307c718c

def z443 : W := mkw 0x89d6c5b540000000 0x089d6c5b54000000 0x81f7f7ff00000007 0x781f7f7ff0000000

def z444 : W := mkw 0x0628180288001408 0x0062818028800140 0x6e381807f8003e0e 0xf6e381807f8003e0

def z445 : W := mkw 0x6ffc9802b9a394a9 0x06ffc9802b9a394a 0x4fb0100339c318c0 0x54fb0100339c318c

def z446 : W := mkw 0x0b40192008001408 0x00b4019200800140 0xefc01ff838003e0d 0xfefc01ff838003e0

def z447 : W := mkw 0x820019a380000000 0x0820019a38000000 0x000011c300000000 0x1000011c30000000

def z448 : W := mkw 0x0002040400000000 0x0000204040000000 0x8007060400000007 0x2800706040000000

def z449 : W := mkw 0x0000000000000000 0x0000000000000000 0x20080800c000c630 0x820080800c000c63

def z450 : W := mkw 0x0097669d469d6356 0xc0097669d469d635 0xb07fee3fc63fe7ff 0xab07fee3fc63fe7f

def z451 : W := mkw 0x4d68a0003132c000 0x04d68a0003132c00 0x6e78e000383fc00a 0xe6e78e000383fc00

def z452 : W := mkw 0x0095000004850000 0x0009500000485000 0x51b7100707c739cf 0x751b7100707c739c

def z453 : W := mkw 0x4d68800031228000 0x04d6880003122800 0x0e00000038000000 0x00e0000003800000

def z454 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001007000039c4 0x100001007000039c

def z455 : W := mkw 0x8ffe9da780000000 0x08ffe9da78000000 0x8fb717c700000007 0x78fb717c70000000

def z456 : W := mkw 0x1b40196029601c08 0x01b40196029601c0 0x6f8019c039c03e0c 0xf6f8019c039c03e0

def z457 : W := mkw 0x3fff1fefbfefbfef 0x83fff1fefbfefbfe 0xffff1fffffffffff 0xfffff1ffffffffff

def z458 : W := mkw 0x1ffc9b682b683e0e 0x01ffc9b682b683e0 0xfffffff83ff83e0f 0xffffffff83ff83e0

def z459 : W := mkw 0x0dfda00004144000 0x00dfda0000414400 0x3fffe000063cc00b 0xe3fffe000063cc00

def z460 : W := mkw 0x4003661c77bfe316 0x44003661c77bfe31 0xf04fee3cffffe73f 0xaf04fee3cffffe73

def z461 : W := mkw 0x26281802980294a9 0x026281802980294a 0x6e380800f807c63a 0xe6e380800f807c63

def z462 : W := mkw 0x26281802980294a9 0x026281802980294a 0x6e381803f803def0 0xd6e381803f803def

def z463 : W := mkw 0x0940000021200000 0x0094000002120000 0x4f80000039c00000 0x44f80000039c0000

def z464 : W := mkw 0x04bd000014878000 0x004bd00001487800 0x7fbf00003fc7c00b 0xe7fbf00003fc7c00

def z465 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xd18707c007c739c9 0x0d18707c007c739c

def z466 : W := mkw 0x009502c106c52944 0x8009502c106c5294 0x51b011c307c739c8 0x551b011c307c739c

def z467 : W := mkw 0x0095000004850000 0x0009500000485000 0x1187000007c00001 0x01187000007c0000

def z468 : W := mkw 0x0003260c061c6316 0x40003260c061c631 0xb0070604063ce73f 0x2b0070604063ce73

def z469 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xb047ee380638260d 0xab047ee380638260

def z470 : W := mkw 0x0200192000000000 0x0020019200000000 0x80001ff800000004 0x180001ff80000000

def z471 : W := mkw 0x26281802980294a9 0x026281802980294a 0x6e30180338033ecc 0xf6e30180338033ec

def z472 : W := mkw 0x12021fed0a483f4e 0x812021fed0a483f4 0x80001fff00003fc4 0x180001fff00003fc

def z473 : W := mkw 0x00016218461c6316 0x400016218461c631 0x3048e838c63ce738 0x83048e838c63ce73

def z474 : W := mkw 0xa6bedc97d80294a9 0x0a6bedc97d80294a 0x6e3ff807f807fffe 0xf6e3ff807f807fff

def z475 : W := mkw 0x66293802bdb7d4a9 0x066293802bdb7d4a 0x7e381807fffffffe 0xf7e381807fffffff

def z476 : W := mkw 0x0095000004850000 0x0009500000485000 0x0037000000070002 0x0003700000007000

def z477 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x0e7fe83fc0000002 0x80e7fe83fc000000

def z478 : W := mkw 0x9b425fffeb683e0e 0x09b425fffeb683e0 0xffc01ffffff83e0d 0xfffc01ffffff83e0

def z479 : W := mkw 0x26bf7edfdedfffff 0xc26bf7edfdedffff 0xffffffffffffffff 0xffffffffffffffff

def z480 : W := mkw 0x000246dd42482b56 0xc000246dd42482b5 0x80001fffc0003ff4 0x180001fffc0003ff

def z481 : W := mkw 0xeffffdb7fdb7d4a9 0x0effffdb7fdb7d4a 0xffffffffffffffff 0xffffffffffffffff

def z482 : W := mkw 0x82005932c0000000 0x082005932c000000 0x00000838c0000000 0x000000838c000000

def z483 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xb04fe638063cc00b 0xab04fe638063cc00

def z484 : W := mkw 0x26281a429a42bcad 0x026281a429a42bca 0xffb81fc7ffc7ffff 0xfffb81fc7ffc7fff

def z485 : W := mkw 0x5fffbfed3fffff4e 0x85fffbfed3fffff4 0xffffffff3fffffcf 0xfffffffff3fffffc

def z486 : W := mkw 0x49d4800021a10000 0x049d4800021a1000 0x0180000001c00000 0x00180000001c0000

def z487 : W := mkw 0xcffffff7f7f7e944 0x8cffffff7f7f7e94 0xfffffffffffff9cf 0xffffffffffffff9c

def z488 : W := mkw 0x89d7e7bd461c6316 0x489d7e7bd461c631 0xb1cfeffcc63ce73f 0xab1cfeffcc63ce73

def z489 : W := mkw 0x0428000010028000 0x0042800001002800 0x4e30000038030000 0x44e3000003803000

def z490 : W := mkw 0x009766dd46dd6b56 0xc009766dd46dd6b5 0xb1cfeffcc7fce73f 0xab1cfeffcc7fce73

def z491 : W := mkw 0x1000036802482a06 0x01000036802482a0 0x800007f800000000 0x0800007f80000000

def z492 : W := mkw 0x0002661c42186316 0x40002661c4218631 0xa048ee3cc038e734 0x8a048ee3cc038e73

def z493 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0x904fe63cc63cc133 0x0904fe63cc63cc13

def z494 : W := mkw 0x1b425f7c6b683f1e 0x41b425f7c6b683f1 0xffc01ffcfff83f3d 0xfffc01ffcfff83f3

def z495 : W := mkw 0x4dffe41475b7c000 0x04dffe41475b7c00 0xffffee3cffffc00f 0xeffffee3cffffc00

def z496 : W := mkw 0x5ffc996039e39c08 0x05ffc996039e39c0 0x4fb011c039c31800 0x54fb011c039c3180

def z497 : W := mkw 0x0001200004144000 0x0000120000414400 0x000fe0000004c002 0x0000fe0000004c00

def z498 : W := mkw 0x4dfc800031a38000 0x04dfc800031a3800 0x6fb8000039c7c00a 0xe6fb8000039c7c00

def z499 : W := mkw 0x00012208061c6316 0x400012208061c631 0x1000000006380000 0x0100000000638000

def z500 : W := mkw 0x89d6c5b540000000 0x089d6c5b54000000 0x81cfeffcc0000007 0xa81cfeffcc000000

def z501 : W := mkw 0x8428c012c0000000 0x08428c012c000000 0x0008e000c0000000 0x00008e000c000000

def z502 : W := mkw 0x0097661c469d6316 0x40097661c469d631 0xf1ffee3cc7ffe73f 0xef1ffee3cc7ffe73

def z503 : W := mkw 0x02037e1c4e1c771e 0x402037e1c4e1c771 0xfe4ffe3cfe3cff3f 0xffe4ffe3cfe3cff3

def z504 : W := mkw 0x8fffddb7c4850140 0x88fffddb7c485014 0x8fffffffc00701c7 0xf8fffffffc00701c

def z505 : W := mkw 0x1b4019282928160a 0x01b4019282928160 0x6e40183838383e0c 0xf6e40183838383e0

def z506 : W := mkw 0x3f681b6abb6abeaf 0x03f681b6abb6abea 0xfff01ffb3ffb3ecd 0xffff01ffb3ffb3ec

def z507 : W := mkw 0x1bd61fed2b683e0e 0x01bd61fed2b683e0 0xfff71fff3ff83e0f 0xffff71fff3ff83e0

def z508 : W := mkw 0x44bda0001497c000 0x044bda0001497c00 0x307fe000063fc00b 0xa307fe000063fc00

def z509 : W := mkw 0x0b437f3c461c6316 0x40b437f3c461c631 0xbfcffffcc63ce73f 0xfbfcffffcc63ce73

def z510 : W := mkw 0x0003641444144110 0x4000364144414411 0x804fee3cc004c137 0xa804fee3cc004c13

def z511 : W := mkw 0x1940036823682a06 0x01940036823682a0 0xffc007f83ff80009 0xeffc007f83ff8000

def z512 : W := mkw 0x242b661ed61ee3b7 0x4242b661ed61ee3b 0xb07fee3fc63fe7ff 0xab07fee3fc63fe7f

def z513 : W := mkw 0x042b661c561ee316 0x4042b661c561ee31 0xfe7fee3cfe3fe73f 0xefe7fee3cfe3fe73

def z514 : W := mkw 0x0000000000000000 0x0000000000000000 0x40301003000318c0 0x540301003000318c

def z515 : W := mkw 0x262938029c16d4a9 0x0262938029c16d4a 0x7e7ff807fe3fffff 0xf7e7ff807fe3ffff

def z516 : W := mkw 0x0000000000000000 0x0000000000000000 0x3040000006380009 0xa304000000638000

def z517 : W := mkw 0x3b401b6aab683eaf 0x03b401b6aab683ea 0xffc01ffffff83ffd 0xfffc01ffffff83ff

def z518 : W := mkw 0x26281a0a9a0ab6af 0x026281a0a9a0ab6a 0xfe781e3ffe3fffff 0xffe781e3ffe3ffff

def z519 : W := mkw 0x9ffedfffe3682a06 0x09ffedfffe3682a0 0x9fffffffc7f80007 0xf9fffffffc7f8000

def z520 : W := mkw 0x4dfc800031a38000 0x04dfc800031a3800 0x7ff000003ffb0009 0xe7ff000003ffb000

def z521 : W := mkw 0x3f681962b9629ca9 0x03f681962b9629ca 0x6fb819c7f9c7fffe 0xf6fb819c7f9c7fff

def z522 : W := mkw 0x8fffffbfc61c6316 0x48fffffbfc61c631 0x9fffffffc6380007 0xf9fffffffc638000

def z523 : W := mkw 0x8fffdfb7c6042104 0x08fffdfb7c604210 0x9fffffffc604210f 0xf9fffffffc604210

def z524 : W := mkw 0x22025e1eca0837bf 0x422025e1eca0837b 0x80001e3fc0003ff4 0x180001e3fc0003ff

def z525 : W := mkw 0x9ffc9bebab683e0e 0x09ffc9bebab683e0 0xfff01ffb3ff83e0d 0xffff01ffb3ff83e0

def z526 : W := mkw 0x24280002900280a1 0x024280002900280a 0x00080000c000c030 0x000080000c000c03

def z527 : W := mkw 0x49d5a00035b7c000 0x049d5a00035b7c00 0x71c7e0003fffc009 0x071c7e0003fffc00

def z528 : W := mkw 0x6ffffe1effbff7bf 0x46ffffe1effbff7b 0xfffffe3fffffffff 0xffffffe3ffffffff

def z529 : W := mkw 0x4d69a00035b7c000 0x04d69a00035b7c00 0x7e48e0003fffc008 0x87e48e0003fffc00

def z530 : W := mkw 0x82037fbfc61c6316 0x482037fbfc61c631 0xb04fffffc63ce73f 0xbb04fffffc63ce73

def z531 : W := mkw 0x1200196008401c08 0x01200196008401c0 0x000011c000001800 0x1000011c00000180

def z532 : W := mkw 0x0003661446146114 0x4000366144614611 0x900fe604c604e13f 0x2900fe604c604e13

def z533 : W := mkw 0x5dfda36837ffea06 0x05dfda36837ffea0 0xffffe7f83fffc00b 0xeffffe7f83fffc00

def z534 : W := mkw 0x99d6c7fd63682a06 0x099d6c7fd63682a0 0x91c7e7f807f80001 0x091c7e7f807f8000

def z535 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xd1b707c007c7000b 0x6d1b707c007c7000

def z536 : W := mkw 0x4d68e018713ac212 0x44d68e018713ac21 0x2e48e838f838c630 0x82e48e838f838c63

def z537 : W := mkw 0x1b421fed2b683f4e 0x81b421fed2b683f4 0xffc01fff3ff83fcd 0xfffc01fff3ff83fc

def z538 : W := mkw 0xcffefdb7f132c000 0x0cffefdb7f132c00 0xaffffffff838c007 0xfaffffffff838c00

def z539 : W := mkw 0x0628180018029408 0x0062818001802940 0x6e3818003807fe0e 0xf6e3818003807fe0

def z540 : W := mkw 0x194003682b683e0e 0x0194003682b683e0 0xf1c007f83ff83e09 0x0f1c007f83ff83e0

def z541 : W := mkw 0x82025db7c0000000 0x082025db7c000000 0x804fffffc0000007 0xb804fffffc000000

def z542 : W := mkw 0x4dfda20837bfe316 0x44dfda20837bfe31 0x7fffe0003fffe73b 0xe7fffe0003fffe73

def z543 : W := mkw 0x000206c502402944 0x8000206c50240294 0xc03017c7000739ce 0x7c03017c7000739c

def z544 : W := mkw 0x0000000800080202 0x0000000080008020 0x2040083800380600 0x8204008380038060

def z545 : W := mkw 0x0097060406852104 0x0009706040685210 0xd1b7060407c7210f 0x6d1b7060407c7210

def z546 : W := mkw 0x100002482b683e0e 0x0100002482b683e0 0xf0400e383ff83e0d 0xaf0400e383ff83e0

def z547 : W := mkw 0x100102482fed3f4e 0x8100102482fed3f4 0x700000003fff3fc8 0x0700000003fff3fc

def z548 : W := mkw 0x22001802880014a9 0x022001802880014a 0x00000800c0000630 0x000000800c000063

def z549 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0x918717c707c039c5 0x1918717c707c039c

def z550 : W := mkw 0x4428a0001012c000 0x04428a0001012c00 0x0008e0000000c000 0x00008e0000000c00

def z551 : W := mkw 0x0003064406c52944 0x80003064406c5294 0xd007060407c739cf 0x2d007060407c739c

def z552 : W := mkw 0x26281802880014a9 0x026281802880014a 0x0e381807c0003ff6 0xf0e381807c0003ff

def z553 : W := mkw 0x0001020006042104 0x0000102000604210 0x1000000006042108 0x0100000000604210

def z554 : W := mkw 0x4001200035b7c000 0x04001200035b7c00 0x704fe0003fffc00b 0xa704fe0003fffc00

def z555 : W := mkw 0x26bc18c398c39ce9 0x826bc18c398c39ce 0x4fb011c339c318c0 0x54fb011c339c318c

def z556 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0x803717c7000739c6 0x1803717c7000739c

def z557 : W := mkw 0x3f68192ab92a96ab 0x03f68192ab92a96a 0x6e78183ff83ffffe 0xf6e78183ff83ffff

def z558 : W := mkw 0x0d68800000000000 0x00d6880000000000 0x0e48e00000000000 0x80e48e0000000000

def z559 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x4fbfe00039c7c002 0x44fbfe00039c7c00

def z560 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0x800fee3cc004e736 0x0800fee3cc004e73

def z561 : W := mkw 0x0001200004144000 0x0000120000414400 0x304fe804c63ce73f 0xa304fe804c63ce73

def z562 : W := mkw 0x4429200035b7c000 0x04429200035b7c00 0x7e3800003fffc00a 0xe7e3800003fffc00

def z563 : W := mkw 0x8ffedfbfc2082206 0x08ffedfbfc208220 0xbfffffffc638260f 0xfbfffffffc638260

def z564 : W := mkw 0x4dffa48535b7c140 0x84dffa48535b7c14 0x7fffe0073fffc1cb 0xe7fffe0073fffc1c

def z565 : W := mkw 0x26bd18029c8794a9 0x026bd18029c8794a 0x7fbf1807ffc7ffff 0xf7fbf1807ffc7fff

def z566 : W := mkw 0x0001000004850000 0x0000100000485000 0x5000000007c70008 0x05000000007c7000

def z567 : W := mkw 0x0002060402002104 0x0000206040200210 0x8000060400002104 0x0800006040000210

def z568 : W := mkw 0x0097649544954150 0xc009764954495415 0x003fe007c007c1f2 0x0003fe007c007c1f

def z569 : W := mkw 0x0000020802082206 0x0000002080208220 0x3000000006382608 0x0300000000638260

def z570 : W := mkw 0x0200180008001408 0x0020018000800140 0x6e30180738073fce 0xf6e30180738073fc

def z571 : W := mkw 0x5dfda2483ffffe0e 0x05dfda2483ffffe0 0x7fffe0003ffffe0b 0xe7fffe0003ffffe0

def z572 : W := mkw 0x0003064406442904 0x0000306440644290 0xd18717c407c4390f 0x7d18717c407c4390

def z573 : W := mkw 0x1943677c677c6b16 0x41943677c677c6b1 0x91c7e7f807f80001 0x091c7e7f807f8000

def z574 : W := mkw 0x8ffedff7c2402944 0x88ffedff7c240294 0x8fffffffc00039c7 0xf8fffffffc00039c

def z575 : W := mkw 0x300002483b6abeaf 0x0300002483b6abea 0x700000003ffffff8 0x0700000003ffffff

def z576 : W := mkw 0x009726c506d56944 0x8009726c506d5694 0xf1fff7c707fff9cf 0xff1fff7c707fff9c

def z577 : W := mkw 0xaffeddb7d80294a9 0x0affeddb7d80294a 0xaffffffff800c637 0xfaffffffff800c63

def z578 : W := mkw 0x1bd51b682fed3e0e 0x01bd51b682fed3e0 0xfff71ff83fff3e0f 0xffff71ff83fff3e0

def z579 : W := mkw 0x20000000180294a9 0x020000000180294a 0x603010073807fffe 0x7603010073807fff

def z580 : W := mkw 0x0001000004040000 0x0000100000404000 0x100700000604000b 0x2100700000604000

def z581 : W := mkw 0x0000000000000000 0x0000000000000000 0x200008000000260c 0xa200008000000260

def z582 : W := mkw 0x0097048504850140 0x8009704850485014 0x51b7000707c701cb 0x651b7000707c701c

def z583 : W := mkw 0x0ffc980280000000 0x00ffc98028000000 0x0ffff807c0000007 0xf0ffff807c000000

def z584 : W := mkw 0x5fffff7c7fffff1e 0x45fffff7c7fffff1 0xfffffffcffffff3f 0xffffffffcffffff3

def z585 : W := mkw 0x26281802980294a9 0x026281802980294a 0x2e381807f800c636 0xf2e381807f800c63

def z586 : W := mkw 0x0f68192280000000 0x00f6819228000000 0x8ff81fffc0000007 0xf8ff81fffc000000

def z587 : W := mkw 0x8f68d932c0000000 0x08f68d932c000000 0x8fc8fff8c0000005 0xf8fc8fff8c000000

def z588 : W := mkw 0x82025fbfc2082316 0x482025fbfc208231 0x80001fffc0002734 0x180001fffc000273

def z589 : W := mkw 0x0dffe61c461c6316 0x40dffe61c461c631 0xbfffee3cc63ce73f 0xebfffee3cc63ce73

def z590 : W := mkw 0x1b40196029601c08 0x01b40196029601c0 0xcfc01ff839c01805 0xfcfc01ff839c0180

def z591 : W := mkw 0x0428000010028000 0x0042800001002800 0x2e0800003800c000 0x82e0800003800c00

def z592 : W := mkw 0x3f681962b9629ca9 0x03f681962b9629ca 0x4fb011c339c318c0 0x54fb011c339c318c

def z593 : W := mkw 0x3b401b683b6abeaf 0x03b401b683b6abea 0xffc01ff83ffffffd 0xfffc01ff83ffffff

def z594 : W := mkw 0x0200180008001408 0x0020018000800140 0x6e081804f804ff3e 0xf6e081804f804ff3

def z595 : W := mkw 0x02001a400a403c0c 0x002001a400a403c0 0xff801fc03fc03e0d 0xfff801fc03fc03e0

def z596 : W := mkw 0x26291a429ec7bded 0x826291a429ec7bde 0x7e381807ffc7fffe 0xf7e381807ffc7fff

def z597 : W := mkw 0x0200180008001408 0x0020018000800140 0x0000180000003e04 0x10000180000003e0

def z598 : W := mkw 0x0000000000000000 0x0000000000000000 0x200800000004c00a 0xa200800000004c00

def z599 : W := mkw 0x4dfda24037f7e804 0x04dfda24037f7e80 0xfffff7c03ffff80f 0xffffff7c03ffff80

def z600 : W := mkw 0x0000621842186216 0x4000062184218621 0xb048ee38c638e63d 0xab048ee38c638e63

def z601 : W := mkw 0x0940000021200000 0x0094000002120000 0x11c0000007f80001 0x011c0000007f8000

def z602 : W := mkw 0x0000000021200000 0x0000000002120000 0x700000003ff80008 0x0700000003ff8000

def z603 : W := mkw 0x0428000010028000 0x0042800001002800 0x6e380804f807e73e 0xe6e380804f807e73

def z604 : W := mkw 0x0000401040000000 0x0000040104000000 0x0048e838c0000000 0x80048e838c000000

def z605 : W := mkw 0x0000000000000000 0x0000000000000000 0x00080004c004c132 0x000080004c004c13

def z606 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0x91b717c707c00007 0x791b717c707c0000

def z607 : W := mkw 0x24280002900280a1 0x024280002900280a 0x00300003000300c0 0x000300003000300c

def z608 : W := mkw 0x8ffc99a380000000 0x08ffc99a38000000 0x0ffff1c300000003 0xf0ffff1c30000000

def z609 : W := mkw 0x22021ec78a403ded 0x822021ec78a403de 0x80001fc7c0003ff4 0x180001fc7c0003ff

def z610 : W := mkw 0x1b411b682fed3f4e 0x81b411b682fed3f4 0xffc01ff83fff3fcd 0xfffc01ff83fff3fc

def z611 : W := mkw 0x1b4079386938561a 0x41b4079386938561 0x2e48e838f838c630 0x82e48e838f838c63

def z612 : W := mkw 0x1b413b682f7c7e0e 0x01b413b682f7c7e0 0xffcffff83ffcfe0f 0xfffcffff83ffcfe0

def z613 : W := mkw 0x0940000021200000 0x0094000002120000 0x2e40000038380000 0x82e4000003838000

def z614 : W := mkw 0x1b401b602b603c0c 0x01b401b602b603c0 0xdf8017c03fc0380d 0x7df8017c03fc0380

def z615 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8fb01fffc0000004 0x58fb01fffc000000

def z616 : W := mkw 0xcffdf932f5b7c000 0x0cffdf932f5b7c00 0x7fffe838ffffc00b 0xe7fffe838ffffc00

def z617 : W := mkw 0x100002480a483e0e 0x0100002480a483e0 0x0000000000003e00 0x00000000000003e0

def z618 : W := mkw 0x84bfc6d7c6c52944 0x884bfc6d7c6c5294 0xd1bff7c7c7c739cf 0x7d1bff7c7c7c739c

def z619 : W := mkw 0x0001000004850140 0x8000100000485014 0x00000000000701c0 0x000000000000701c

def z620 : W := mkw 0x0000000010028000 0x0000000001002800 0x600000003807c008 0x0600000003807c00

def z621 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0x9047e63c063c210f 0x29047e63c063c210

def z622 : W := mkw 0x3f681b6abb6abeaf 0x03f681b6abb6abea 0xffc81ff8fff8fe3d 0xfffc81ff8fff8fe3

def z623 : W := mkw 0xdffffffffffffe0e 0x0dffffffffffffe0 0xfffffffffffffe0f 0xffffffffffffffe0

def z624 : W := mkw 0x84bc808380000000 0x084bc80838000000 0x0030000300000000 0x0003000030000000

def z625 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0x918707c407c4210f 0x2918707c407c4210

def z626 : W := mkw 0x0943661c673c6316 0x40943661c673c631 0xffcfee3cfffce73f 0xeffcfee3cfffce73

def z627 : W := mkw 0x09d706c527e52944 0x809d706c527e5294 0xfff717c73fff39cf 0xffff717c73fff39c

def z628 : W := mkw 0x0000020802082206 0x0000002080208220 0x9040063806380001 0x0904006380638000

def z629 : W := mkw 0x00012208061c6316 0x400012208061c631 0x30080804c63ce73e 0xa30080804c63ce73

def z630 : W := mkw 0x100000082928160a 0x0100000082928160 0x2000000038380600 0x0200000003838060

def z631 : W := mkw 0x0003461c460c2316 0x40003461c460c231 0x90070e3cc604273f 0x290070e3cc604273

def z632 : W := mkw 0x4dfda0001497c000 0x04dfda0001497c00 0x0fffe0000007c003 0xe0fffe0000007c00

def z633 : W := mkw 0x0000024802482a06 0x00000024802482a0 0xf1c01ff807f83e0d 0xff1c01ff807f83e0

def z634 : W := mkw 0x0094000000000000 0x0009400000000000 0x01b7000000000003 0x601b700000000000

def z635 : W := mkw 0x26281802980294a9 0x026281802980294a 0x4e381007f807d9f2 0x54e381007f807d9f

def z636 : W := mkw 0x8ffc99a380000000 0x08ffc99a38000000 0x0fb819c7c0000006 0xf0fb819c7c000000

def z637 : W := mkw 0x5bd5bb682ffd7e0e 0x05bd5bb682ffd7e0 0xffc7fff83ff83e0d 0xfffc7fff83ff83e0

def z638 : W := mkw 0x0000020802082316 0x4000002080208231 0x0000000000002730 0x0000000000000273

def z639 : W := mkw 0x0b401b2802082206 0x00b401b280208220 0xbfc01ff80638260d 0xfbfc01ff80638260

def z640 : W := mkw 0x000206c502402944 0x8000206c50240294 0x800007c000000000 0x0800007c00000000

def z641 : W := mkw 0x4dfca0003132c000 0x04dfca0003132c00 0x2fffe0003838c003 0xe2fffe0003838c00

def z642 : W := mkw 0x26281802980294a9 0x026281802980294a 0x4e301007380739ce 0x74e301007380739c

def z643 : W := mkw 0x0000000000000000 0x0000000000000000 0x80400e3800000005 0xa80400e380000000

def z644 : W := mkw 0x5ffdb9283dbfd60a 0x05ffdb9283dbfd60 0x7fffe8383fffc60b 0xe7fffe8383fffc60

def z645 : W := mkw 0x0000000000000000 0x0000000000000000 0x5180000007c00009 0x65180000007c0000

def z646 : W := mkw 0x0200180008001408 0x0020018000800140 0x2e00080038000600 0x82e0008003800060

def z647 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x0fbff1c7c0000002 0x50fbff1c7c000000

def z648 : W := mkw 0x0002461c42082316 0x40002461c4208231 0xa0080e3cc004e73e 0xaa0080e3cc004e73

def z649 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0x904fee3cc6380007 0xa904fee3cc638000

def z650 : W := mkw 0x4dfde01875bfc212 0x44dfde01875bfc21 0x7fffe838ffffc63b 0xe7fffe838ffffc63

def z651 : W := mkw 0x0428000010028000 0x0042800001002800 0x6e3810073807f9ce 0xf6e3810073807f9c

def z652 : W := mkw 0x4095a00004954000 0x04095a0000495400 0x0007e00000000000 0x00007e0000000000

def z653 : W := mkw 0x36281a4abb6abeaf 0x036281a4abb6abea 0x7e381807fffffffe 0xf7e381807fffffff

def z654 : W := mkw 0x0001024006c52944 0x80001024006c5294 0x5030100707c739ce 0x75030100707c739c

def z655 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000000739c8 0x040000000000739c

def z656 : W := mkw 0x0000601840184212 0x4000060184018421 0x2048e83cc03ce73e 0xa2048e83cc03ce73

def z657 : W := mkw 0x109706cd2fed3f4e 0x8109706cd2fed3f4 0xf1b717c73fff3fcf 0x7f1b717c73fff3fc

def z658 : W := mkw 0x8ffc99e380c10840 0x88ffc99e380c1084 0x4fb011c301c318c0 0x54fb011c301c318c

def z659 : W := mkw 0x89d7e7bd461c6316 0x489d7e7bd461c631 0x91c7e7f806380001 0x091c7e7f80638000

def z660 : W := mkw 0x44bda0001497c000 0x044bda0001497c00 0x6e3fe0003807c00a 0xe6e3fe0003807c00

def z661 : W := mkw 0x1940016021600800 0x0194001602160080 0x018001c001c00000 0x0018001c001c0000

def z662 : W := mkw 0x00012208061c6316 0x400012208061c631 0xb0400e38063ce73d 0xab0400e38063ce73

def z663 : W := mkw 0x1bd71fe52fe53d4c 0x81bd71fe52fe53d4 0xdfb717c73fc739cf 0x7dfb717c73fc739c

def z664 : W := mkw 0x22001802880014a9 0x022001802880014a 0x20081807c004fffe 0xb20081807c004fff

def z665 : W := mkw 0x0000020002002004 0x0000002000200200 0x900006000600200d 0x2900006000600200

def z666 : W := mkw 0x02971ec50ec53d4c 0x802971ec50ec53d4 0xffb71fc73fc73fcf 0xfffb71fc73fc73fc

def z667 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xd18717c007c0380d 0x7d18717c007c0380

def z668 : W := mkw 0x0628180280000000 0x0062818028000000 0x4e381807c00739ce 0xf4e381807c00739c

def z669 : W := mkw 0x0002441440000110 0x4000244144000011 0x00000004c0000130 0x000000004c000013

def z670 : W := mkw 0x20000000080014a9 0x020000000080014a 0x0000000000003ff0 0x00000000000003ff

def z671 : W := mkw 0x4dfca00031b3c000 0x04dfca00031b3c00 0x6ff8e00039fbc000 0xc6ff8e00039fbc00

def z672 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7fb000003fffc008 0x47fb000003fffc00

def z673 : W := mkw 0x8940c13040000000 0x08940c1304000000 0x0040e03800000000 0x00040e0380000000

def z674 : W := mkw 0x32001b6a8a483eaf 0x032001b6a8a483ea 0x80001fffc0003ff4 0x180001fffc0003ff

def z675 : W := mkw 0x44bc800010838000 0x044bc80001083800 0x0030000000030000 0x0003000000003000

def z676 : W := mkw 0x6ffdb802bdb7d4a9 0x06ffdb802bdb7d4a 0x7fffe800ffffc63b 0xe7fffe800ffffc63

def z677 : W := mkw 0x0003260406146104 0x0000326040614610 0xb04fe604063ce10f 0xab04fe604063ce10

def z678 : W := mkw 0x26281802980294a9 0x026281802980294a 0x6e080800f807fff8 0x86e080800f807fff

def z679 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xcf801ff839c03e04 0x5cf801ff839c03e0

def z680 : W := mkw 0x80024497c0000000 0x080024497c000000 0x00000007c0000000 0x000000007c000000

def z681 : W := mkw 0x36281b6a9a4abeaf 0x036281b6a9a4abea 0xee381ffff807fffe 0xfee381ffff807fff

def z682 : W := mkw 0x8fffddb7c4850000 0x08fffddb7c485000 0xdfffffffc7c7000f 0xfdfffffffc7c7000

def z683 : W := mkw 0x0000020802082206 0x0000002080208220 0x80000e3800002604 0x080000e380000260

def z684 : W := mkw 0x12037f7c4e5c7f1e 0x412037f7c4e5c7f1 0xb04ffffcc63cff3f 0xbb04ffffcc63cff3

def z685 : W := mkw 0x0095024006c52944 0x80095024006c5294 0x51b7000007c739cb 0x651b7000007c739c

def z686 : W := mkw 0x1bd419e129e11c48 0x81bd419e129e11c4 0x4fb011c339c318c0 0x54fb011c339c318c

def z687 : W := mkw 0x0003060406042104 0x0000306040604210 0xb00f0e04c604e73f 0xab00f0e04c604e73

def z688 : W := mkw 0x4dfc80c131e38840 0x84dfc80c131e3884 0x4fb011c339c318c0 0x54fb011c339c318c

def z689 : W := mkw 0x0940024023602804 0x0094002402360280 0xffc017c03ff8380d 0xfffc017c03ff8380

def z690 : W := mkw 0x4095200035b7c000 0x04095200035b7c00 0x71b700003fffc00b 0x671b700003fffc00

def z691 : W := mkw 0x22037e1ece1c77bf 0x422037e1ece1c77b 0xb04ffe3fc63cffff 0xbb04ffe3fc63cfff

def z692 : W := mkw 0x209706c51ec7bded 0x8209706c51ec7bde 0xf1b717c73fc7ffff 0x7f1b717c73fc7fff

def z693 : W := mkw 0x0000000000000000 0x0000000000000000 0x0030100700000006 0x7003010070000000

def z694 : W := mkw 0x0003461446042104 0x0000346144604210 0x904fee3cc604210f 0xa904fee3cc604210

def z695 : W := mkw 0xaf68d932d80294a9 0x0af68d932d80294a 0x6e78f83ff807fffe 0xf6e78f83ff807fff

def z696 : W := mkw 0x1940012821280202 0x0194001282128020 0x0040003800380000 0x0004000380038000

def z697 : W := mkw 0x4ffdb8003db7d408 0x04ffdb8003db7d40 0x7ffff8003ffffe0f 0xf7ffff8003ffffe0

def z698 : W := mkw 0x9ffedfffca483e0e 0x09ffedfffca483e0 0x8fffffffc0003e07 0xf8fffffffc0003e0

def z699 : W := mkw 0x12001b682b683e0e 0x012001b682b683e0 0xf0001ff83ff83e0c 0x1f0001ff83ff83e0

def z700 : W := mkw 0x009606c502402944 0x8009606c50240294 0x81b717c7000039c7 0x781b717c7000039c

def z701 : W := mkw 0x0000000000000000 0x0000000000000000 0x400010000000380c 0x7400010000000380

def z702 : W := mkw 0x8f6bff3ec61c6316 0x48f6bff3ec61c631 0xbe4fee3cc63ce73f 0xabe4fee3cc63ce73

def z703 : W := mkw 0x86bedc97c0000000 0x086bedc97c000000 0x0e3ff807c0000006 0xf0e3ff807c000000

def z704 : W := mkw 0x9ffc99e3a9601c08 0x09ffc99e3a9601c0 0x4fb011c339c01800 0x54fb011c339c0180

def z705 : W := mkw 0x0001024006c52944 0x80001024006c5294 0xd18017c007c739cd 0x7d18017c007c739c

def z706 : W := mkw 0xcffc99a3b1a38000 0x0cffc99a3b1a3800 0x4fb011c339c30000 0x54fb011c339c3000

def z707 : W := mkw 0x89d6c5b540000000 0x089d6c5b54000000 0x81cfe7fcc0000003 0x081cfe7fcc000000

def z708 : W := mkw 0x009460d940d94a52 0xc009460d940d94a5 0x61f8f9fbc1fbdef0 0xd61f8f9fbc1fbdef

def z709 : W := mkw 0x6dfda002b5b7c0a1 0x06dfda002b5b7c0a 0x7fffe000ffffc03b 0xe7fffe000ffffc03

def z710 : W := mkw 0xaffeddb7d80294a9 0x0affeddb7d80294a 0xcffffffff80739cf 0xfcffffffff80739c

def z711 : W := mkw 0x262b7e1ede1ef7bf 0x4262b7e1ede1ef7b 0xde77f63b3e3b18c1 0x5de77f63b3e3b18c

def z712 : W := mkw 0x1b401b682b683f4e 0x81b401b682b683f4 0xffc01ff83ff83fcd 0xfffc01ff83ff83fc

def z713 : W := mkw 0x0bd65db540000000 0x00bd65db54000000 0x8fffffffc0000007 0xf8fffffffc000000

def z714 : W := mkw 0x89d6c5b540000000 0x089d6c5b54000000 0x81f7f7fb00000001 0x581f7f7fb0000000

def z715 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xf1cfee3cc7fce73f 0xef1cfee3cc7fce73

def z716 : W := mkw 0x00016018441c4212 0x400016018441c421 0x304fe83cc63ce73f 0xa304fe83cc63ce73

def z717 : W := mkw 0x3f68192ab92a96ab 0x03f68192ab92a96a 0x2e40083838380600 0x82e4008383838060

def z718 : W := mkw 0x8ffeddb7c8001408 0x08ffeddb7c800140 0xeffffffff804ff3f 0xfeffffffff804ff3

def z719 : W := mkw 0x0096449540000000 0x0009644954000000 0xe1ffffffc007ffff 0xfe1ffffffc007fff

def z720 : W := mkw 0x009644d540c10840 0x8009644d540c1084 0xc1ffffffc1c318c7 0xfc1ffffffc1c318c

def z721 : W := mkw 0x009400c100c10840 0x8009400c100c1084 0x41b011c701c719c2 0x541b011c701c719c

def z722 : W := mkw 0x24280002980294a9 0x024280002980294a 0x6e380007f807fffa 0xe6e380007f807fff

def z723 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xb04fee38c638e63d 0xab04fee38c638e63

def z724 : W := mkw 0x009502c106c52944 0x8009502c106c5294 0x51b011c707c739ce 0x751b011c707c739c

def z725 : W := mkw 0x8ffeddb7c0810040 0x88ffeddb7c081004 0x8fffffffc00300c7 0xf8fffffffc00300c

def z726 : W := mkw 0x94bec6dfeb683e0e 0x094bec6dfeb683e0 0x703fe007fff83e0a 0x0703fe007fff83e0

def z727 : W := mkw 0x009402c102c12944 0x8009402c102c1294 0x41b011c301c339c0 0x541b011c301c339c

def z728 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xd1b717c707c339c5 0x5d1b717c707c339c

def z729 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x81ffffffc0000007 0x181ffffffc000000

def z730 : W := mkw 0x0096449540000000 0x0009644954000000 0x81c7e7f800000001 0x081c7e7f80000000

def z731 : W := mkw 0x8ffeddb7e9201408 0x08ffeddb7e920140 0xfffffffffff83e0f 0xffffffffffff83e0

def z732 : W := mkw 0x4941200035b7c000 0x04941200035b7c00 0x7fcfe0003fffc00b 0xe7fcfe0003fffc00

def z733 : W := mkw 0x8bd6ddb540000000 0x08bd6ddb54000000 0x8fc7eff800000001 0x88fc7eff80000000

def z734 : W := mkw 0x89d6c5b540000000 0x089d6c5b54000000 0x81cfe7f800000003 0xa81cfe7f80000000

def z735 : W := mkw 0x0003641c441c4212 0x40003641c441c421 0xb04fee3cc63cc63f 0xab04fee3cc63cc63

def z736 : W := mkw 0x009726cd06dd6b46 0x8009726cd06dd6b4 0xf1ffffff07ffffcf 0xff1ffffff07ffffc

def z737 : W := mkw 0x009402c902c92a46 0x8009402c902c92a4 0xf1f01ffb07fb3ecd 0xff1f01ffb07fb3ec

def z738 : W := mkw 0x8f69db72c6c52944 0x88f69db72c6c5294 0x5e48e838c7c739c8 0x85e48e838c7c739c

def z739 : W := mkw 0x0002461c42082206 0x00002461c4208220 0xb04fee3cc63ce73f 0xab04fee3cc63ce73

def z740 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xfff81fffffffffff 0xffff81ffffffffff

def z741 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8fcfeffcc0000007 0xa8fcfeffcc000000

def z742 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0x51b711c707c739ca 0x551b711c707c739c

def z743 : W := mkw 0x8ffeddb7d0028000 0x08ffeddb7d002800 0xaffffffff800c007 0xfaffffffff800c00

def z744 : W := mkw 0x0dfc812000000000 0x00dfc81200000000 0x8fffe7f800000003 0xe8fffe7f80000000

def z745 : W := mkw 0x0dfec49540000000 0x00dfec4954000000 0x8fffffffc0000007 0xf8fffffffc000000

def z746 : W := mkw 0xaffeddb7d00280a1 0x0affeddb7d00280a 0xcfffffffc007f9ff 0xfcfffffffc007f9f

def z747 : W := mkw 0x12025ffd4a483f5e 0xc12025ffd4a483f5 0x80001fffc0003ff4 0x180001fffc0003ff

def z748 : W := mkw 0x92025fffca483f1e 0x492025fffca483f1 0x80001fffc0003f34 0x180001fffc0003f3

def z749 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xdfc01ff83ff81805 0xfdfc01ff83ff8180

def z750 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x3fcfe0003ffcc00b 0xa3fcfe0003ffcc00

def z751 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xff801ff83ff83e0c 0x5ff801ff83ff83e0

def z752 : W := mkw 0x009606c502c12944 0x8009606c502c1294 0xc1b017c701c739ce 0x7c1b017c701c739c

def z753 : W := mkw 0xa2025db7c80014a9 0x0a2025db7c80014a 0xa04fffffc004ffff 0xba04fffffc004fff

def z754 : W := mkw 0x0b40192029201408 0x00b4019202920140 0xffc01ff83ff83e0d 0xfffc01ff83ff83e0

def z755 : W := mkw 0x56bdbb681edffe0e 0x056bdbb681edffe0 0x803ffff80007fe06 0x1803ffff80007fe0

def z756 : W := mkw 0xabd6ddb7c80014a9 0x0abd6ddb7c80014a 0x81c7ffffc0003ff5 0x181c7ffffc0003ff

def z757 : W := mkw 0x9ffeddb7e9201408 0x09ffeddb7e920140 0x8ffffffff8000007 0xf8ffffffff800000

def z758 : W := mkw 0x100122480e5c7f1e 0x4100122480e5c7f1 0x30000000063cff38 0x030000000063cff3

def z759 : W := mkw 0xc2037db7f5b7c000 0x0c2037db7f5b7c00 0xf0001fffffffc00c 0x1f0001fffffffc00

def z760 : W := mkw 0x8ffdbbab861c6316 0x48ffdbbab861c631 0x3fb011c3063ce738 0x53fb011c3063ce73

def z761 : W := mkw 0x00016018441c4212 0x400016018441c421 0x204fe838c03cc632 0x8204fe838c03cc63

def z762 : W := mkw 0xef68f932f932d4a9 0x0ef68f932f932d4a 0x2e48e838f838c630 0x82e48e838f838c63

def z763 : W := mkw 0x6bd5b802adb554a9 0x06bd5b802adb554a 0x11c7f807c7f83ff5 0x111c7f807c7f83ff

def z764 : W := mkw 0xaffeddb7d80294a9 0x0affeddb7d80294a 0xeffffffff807c63f 0xfeffffffff807c63

def z765 : W := mkw 0x8ffeddb7e1200000 0x08ffeddb7e120000 0xcffffffff9c00007 0xfcffffffff9c0000

def z766 : W := mkw 0x0dfd800025a50000 0x00dfd800025a5000 0x7fffe0003fff000b 0xe7fffe0003fff000

def z767 : W := mkw 0x1b401b682b683f1e 0x41b401b682b683f1 0xffc01ff83ff83f3d 0xfffc01ff83ff83f3

def z768 : W := mkw 0x89d6c5b561200000 0x089d6c5b56120000 0xffc7e7f83ff80009 0xeffc7e7f83ff8000

def z769 : W := mkw 0xa9d6c5b5580294a9 0x0a9d6c5b5580294a 0xe1c7e7f83807fff9 0x0e1c7e7f83807fff

def z770 : W := mkw 0x0428000010028000 0x0042800001002800 0x6e381807f807fffe 0xf6e381807f807fff

def z771 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xf1b71fc707c73fcf 0xff1b71fc707c73fc

def z772 : W := mkw 0x8dfec5b540000000 0x08dfec5b54000000 0x8fcfe7f800000001 0x88fcfe7f80000000

def z773 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8ff7f7ff00000007 0x78ff7f7ff0000000

def z774 : W := mkw 0x26281802980294a9 0x026281802980294a 0x6e380807f807fffa 0x86e380807f807fff

def z775 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8fc7e7f800000001 0x08fc7e7f80000000

def z776 : W := mkw 0x4dfda08135b7c040 0x84dfda08135b7c04 0x7fffe0033fffc0cb 0xe7fffe0033fffc0c

def z777 : W := mkw 0x009746dd46cd2b56 0xc009746dd46cd2b5 0xd1ffffffc7c73fff 0xfd1ffffffc7c73ff

def z778 : W := mkw 0x1b437d746d745d18 0x41b437d746d745d1 0x4f8ff1c4f9c4d932 0x54f8ff1c4f9c4d93

def z779 : W := mkw 0x1bd71dad2dad174a 0x81bd71dad2dad174 0x2e77083f383f07c2 0x82e77083f383f07c

def z780 : W := mkw 0x000206c502402944 0x8000206c50240294 0xd1b017c707c739cf 0x7d1b017c707c739c

def z781 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xbfc01ff83ff80605 0xfbfc01ff83ff8060

def z782 : W := mkw 0x4001224837ffeb56 0xc4001224837ffeb5 0x700000003ffffff8 0x0700000003ffffff

def z783 : W := mkw 0x0000601840184212 0x4000060184018421 0x204fe838c038c633 0xa204fe838c038c63

def z784 : W := mkw 0x0003665c465c6b56 0xc0003665c465c6b5 0xb04fee3cc63cffff 0xab04fee3cc63cfff

def z785 : W := mkw 0x862a5db7c0000000 0x0862a5db7c000000 0x8e7fffffc0000007 0xf8e7fffffc000000

def z786 : W := mkw 0x0ffc992018029408 0x00ffc99201802940 0xeffffff83807fe0f 0xfeffffff83807fe0

def z787 : W := mkw 0x009522c906dd6b56 0xc009522c906dd6b5 0x71b011c307fffff8 0x571b011c307fffff

def z788 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xd1b717c707c719c3 0x5d1b717c707c719c

def z789 : W := mkw 0x8f6addb7c0000000 0x08f6addb7c000000 0x8e4fffffc0000007 0xb8e4fffffc000000

def z790 : W := mkw 0x26281802980294a9 0x026281802980294a 0x6e381007f807fffa 0x56e381007f807fff

def z791 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7fffe0073fffc1cb 0xe7fffe0073fffc1c

def z792 : W := mkw 0x8ffeddb7f1228000 0x08ffeddb7f122800 0xffffffffffffc00f 0xfffffffffffffc00

def z793 : W := mkw 0x4b41392035b7c000 0x04b41392035b7c00 0xffc01ff83fffc00d 0xfffc01ff83fffc00

def z794 : W := mkw 0x0003641c441c4312 0x40003641c441c431 0x204fe838c038c630 0x8204fe838c038c63

def z795 : W := mkw 0x0dfc800031228000 0x00dfc80003122800 0x7fffe0003fffc00b 0xe7fffe0003fffc00

def z796 : W := mkw 0x0003665c46dd6b56 0xc0003665c46dd6b5 0xf07ffe3fc7ffffff 0xff07ffe3fc7fffff

def z797 : W := mkw 0x8f6add36c0000000 0x08f6add36c000000 0x8fcffffcc0000007 0xf8fcffffcc000000

def z798 : W := mkw 0x800245b540000000 0x0800245b54000000 0x8047e7f800000001 0x08047e7f80000000

def z799 : W := mkw 0x6dfda002b5b7c0a1 0x06dfda002b5b7c0a 0x7fffe807ffffe7ff 0xe7fffe807ffffe7f

def z800 : W := mkw 0x8bd6ddb540000000 0x08bd6ddb54000000 0x8fc7f7f800000001 0x58fc7f7f80000000

def z801 : W := mkw 0xcffeddb7f1228000 0x0cffeddb7f122800 0x8ffffffff8000007 0xf8ffffffff800000

def z802 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7ffff0003ffff80f 0xf7ffff0003ffff80

def z803 : W := mkw 0x26bf1ec79ec7bded 0x826bf1ec79ec7bde 0xbf8f0fc0ffc0c631 0x8bf8f0fc0ffc0c63

def z804 : W := mkw 0x89d6c5b561200000 0x089d6c5b56120000 0x91c7e7f807f80001 0x091c7e7f807f8000

def z805 : W := mkw 0x0097048504850000 0x0009704850485000 0xd1b717c707c739cf 0x7d1b717c707c739c

def z806 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0xffffee383fffc00f 0xeffffee383fffc00

def z807 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xa04fee3cc03ce736 0x8a04fee3cc03ce73

def z808 : W := mkw 0x0940024823682a06 0x00940024823682a0 0xffc01ff83ff83e0d 0xfffc01ff83ff83e0

def z809 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xd1bf17c7c7c7f9ff 0x7d1bf17c7c7c7f9f

def z810 : W := mkw 0x009706cd06cd2b56 0xc009706cd06cd2b5 0xd1b717c707c73fff 0x7d1b717c707c73ff

def z811 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xc1b717c701c739c6 0x5c1b717c701c739c

def z812 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0xbfffffffc638000f 0xfbfffffffc638000

def z813 : W := mkw 0x12013a482f7c7f1e 0x412013a482f7c7f1 0x7e081804fffcff3e 0xf7e081804fffcff3

def z814 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0x9fc007f83ff80001 0x09fc007f83ff8000

def z815 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0xcfffffffc00318c7 0xfcfffffffc00318c

def z816 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7fcfe0003fffc009 0x87fcfe0003fffc00

def z817 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7ff7e0003ffb0009 0xe7ff7e0003ffb000

def z818 : W := mkw 0x0003665c465c6b16 0x40003665c465c6b1 0xf04fee3cc7fcff3f 0xaf04fee3cc7fcff3

def z819 : W := mkw 0x8bd6ddb540000000 0x08bd6ddb54000000 0x8ff7ffff00000007 0xf8ff7ffff0000000

def z820 : W := mkw 0x0002641c40184212 0x40002641c4018421 0xa04fee38c038c631 0x8a04fee38c038c63

def z821 : W := mkw 0x009746dd46cd2b56 0xc009746dd46cd2b5 0xf1f71fffc7ff3fff 0xff1f71fffc7ff3ff

def z822 : W := mkw 0x26be5c97d80294a9 0x026be5c97d80294a 0xeffffffff807ffff 0xfeffffffff807fff

def z823 : W := mkw 0x02001a480a483e0e 0x002001a480a483e0 0xffc01ff83ff83e0d 0xfffc01ff83ff83e0

def z824 : W := mkw 0x89d6c5b540000000 0x089d6c5b54000000 0x81c7effcc0000005 0x081c7effcc000000

def z825 : W := mkw 0x009766dd46dd6b56 0xc009766dd46dd6b5 0xf1f7f7ff07ffffff 0x7f1f7f7ff07fffff

def z826 : W := mkw 0x009400c100c10840 0x8009400c100c1084 0x41b711c301c318c3 0x741b711c301c318c

def z827 : W := mkw 0xaffeddb7d00280a1 0x0affeddb7d00280a 0xafffffffc007e7ff 0xfafffffffc007e7f

def z828 : W := mkw 0x4dfda12035b7c000 0x04dfda12035b7c00 0xffffe7f83fffc00b 0xeffffe7f83fffc00

def z829 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x5ff7e0003fff000b 0x65ff7e0003fff000

def z830 : W := mkw 0xaffeddb7d80294a9 0x0affeddb7d80294a 0xaffffffff807c7f7 0xfaffffffff807c7f

def z831 : W := mkw 0x3d68036ab36aaaa7 0x03d68036ab36aaaa 0x91f807ffc7ffc1f3 0x091f807ffc7ffc1f

def z832 : W := mkw 0x4dfec61c73aba316 0x44dfec61c73aba31 0xcfb00e3cf9c32734 0x4cfb00e3cf9c3273

def z833 : W := mkw 0x19d767fd67fd6b56 0xc19d767fd67fd6b5 0x91c7e7f807f80001 0x091c7e7f807f8000

def z834 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7fffe804ffffc00f 0xe7fffe804ffffc00

def z835 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8fcffff8c0000005 0xf8fcffff8c000000

def z836 : W := mkw 0x0096449540000000 0x0009644954000000 0x81f7f7ff00000007 0x781f7f7ff0000000

def z837 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8fbfffffc0000006 0x58fbfffffc000000

def z838 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xb1cffffcc63ce73f 0xfb1cffffcc63ce73

def z839 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xd1fff7c707c739cf 0xfd1fff7c707c739c

def z840 : W := mkw 0xc4bfe497d497c110 0x4c4bfe497d497c11 0x003fe007c007c132 0x0003fe007c007c13

def z841 : W := mkw 0x0002661c42186316 0x40002661c4218631 0xa04fee3cc038e737 0xaa04fee3cc038e73

def z842 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8fffefffc0000003 0x88fffefffc000000

def z843 : W := mkw 0x009726cd06dd6b56 0xc009726cd06dd6b5 0xf1bf1fc7c7ffffff 0xff1bf1fc7c7fffff

def z844 : W := mkw 0x8ffeddb7c0000140 0x88ffeddb7c000014 0x8fffffffc00001c7 0xf8fffffffc00001c

def z845 : W := mkw 0xaffeddb7d80294a9 0x0affeddb7d80294a 0xcff7f7fb380318c1 0x5cff7f7fb380318c

def z846 : W := mkw 0x89d6c5b540000000 0x089d6c5b54000000 0x81f7e7ff00000003 0x081f7e7ff0000000

def z847 : W := mkw 0x92025fffca483f4e 0x892025fffca483f4 0x80001fffc0003fc4 0x180001fffc0003fc

def z848 : W := mkw 0xaffeddb7c80014a9 0x0affeddb7c80014a 0x8fffffffc0000637 0xf8fffffffc000063

def z849 : W := mkw 0x009766d546d56954 0xc009766d546d5695 0xf1bfffc7c7c7ffff 0xff1bfffc7c7c7fff

def z850 : W := mkw 0x0000004000400800 0x0000000400040080 0x41b011c701c739ce 0x741b011c701c739c

def z851 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xdfc01ff83ff83e05 0x5dfc01ff83ff83e0

def z852 : W := mkw 0x89d6c5b540000000 0x089d6c5b54000000 0x81c7eff800000005 0xa81c7eff80000000

def z853 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7fffe0003fffe73b 0xe7fffe0003fffe73

def z854 : W := mkw 0x0003665c465c6b16 0x40003665c465c6b1 0xb04ffffcc63cff3f 0xbb04ffffcc63cff3

def z855 : W := mkw 0x3b401b6aab683eaf 0x03b401b6aab683ea 0xffc01ff8fff83e3d 0xfffc01ff8fff83e3

def z856 : W := mkw 0x8dfec5b540000000 0x08dfec5b54000000 0x8ffff7ff00000007 0xf8ffff7ff0000000

def z857 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xdfc017f83ff8380d 0x7dfc017f83ff8380

def z858 : W := mkw 0x0003665c46dd6b56 0xc0003665c46dd6b5 0xb04fee3cc7fce73f 0xab04fee3cc7fce73

def z859 : W := mkw 0x0003665c465c6b16 0x40003665c465c6b1 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z860 : W := mkw 0xaffeddb7d80294a9 0x0affeddb7d80294a 0xeffffffff807d8cf 0xfeffffffff807d8c

def z861 : W := mkw 0xeffeddb7f9a394a9 0x0effeddb7f9a394a 0xcffffffff9c318c7 0xfcffffffff9c318c

def z862 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8fffffffc004c137 0xf8fffffffc004c13

def z863 : W := mkw 0xeffc99a3b9a394a9 0x0effc99a3b9a394a 0x4fb011c339c318c0 0x54fb011c339c318c

def z864 : W := mkw 0x4d69a00035b7c000 0x04d69a00035b7c00 0x7e4fe0003fffc00b 0xa7e4fe0003fffc00

def z865 : W := mkw 0x6dfda002b5b7c0a1 0x06dfda002b5b7c0a 0x7fffe0033fffc0cb 0xe7fffe0033fffc0c

def z866 : W := mkw 0x0dfda00025344000 0x00dfda0002534400 0x7fffe0003ffcc00b 0xe7fffe0003ffcc00

def z867 : W := mkw 0x009726c506d56944 0x8009726c506d5694 0xf1ffffc7c7ffffff 0xff1ffffc7c7fffff

def z868 : W := mkw 0x0002441440000000 0x0000244144000000 0x81cffffcc0000007 0xf81cffffcc000000

def z869 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xf1f717c707ff39cf 0xff1f717c707ff39c

def z870 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0xefffffffc007ffff 0xfefffffffc007fff

def z871 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xffc00ff83ff80609 0xeffc00ff83ff8060

def z872 : W := mkw 0x26281922980294a9 0x026281922980294a 0xee381ffff807fffe 0xfee381ffff807fff

def z873 : W := mkw 0x009604c500c10840 0x8009604c500c1084 0xc1b717c701c739cf 0x7c1b717c701c739c

def z874 : W := mkw 0xaffeddb7d00280a1 0x0affeddb7d00280a 0xeffffffff807c1ff 0xfeffffffff807c1f

def z875 : W := mkw 0x009746dd46cd2b46 0x8009746dd46cd2b4 0xf1ffffffc7ff3fcf 0xff1ffffffc7ff3fc

def z876 : W := mkw 0x82965db7c0000000 0x082965db7c000000 0x81ffffffc0000007 0xf81ffffffc000000

def z877 : W := mkw 0x26293a4a9edfffff 0xc26293a4a9edffff 0x7e381807fffffffe 0xf7e381807fffffff

def z878 : W := mkw 0x2f6a5d36d80294a9 0x02f6a5d36d80294a 0xeffffffff807ffff 0xfeffffffff807fff

def z879 : W := mkw 0xaffeddb7d80294a9 0x0affeddb7d80294a 0xeffffffff800fe3f 0xfeffffffff800fe3

def z880 : W := mkw 0x0941200025344000 0x0094120002534400 0x7fc7e0003ff80009 0xe7fc7e0003ff8000

def z881 : W := mkw 0x8ffeddb7e1200000 0x08ffeddb7e120000 0x9fffffffc7f80007 0xf9fffffffc7f8000

def z882 : W := mkw 0x82025db7c0000000 0x082025db7c000000 0x800fffffc0000006 0x1800fffffc000000

def z883 : W := mkw 0x009746d546c52944 0x8009746d546c5294 0xd1b71fffc7c739cf 0x7d1b71fffc7c739c

def z884 : W := mkw 0x1940036823682a06 0x01940036823682a0 0xdfc007f83ff80001 0x4dfc007f83ff8000

def z885 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xffc81ff8fff8fe3d 0xfffc81ff8fff8fe3

def z886 : W := mkw 0x0003669d461c6356 0xc0003669d461c635 0xb04fee3fc63ce7ff 0xab04fee3fc63ce7f

def z887 : W := mkw 0x009704c504c50940 0x8009704c504c5094 0x41b711c701c739ce 0x741b711c701c739c

def z888 : W := mkw 0x86beddb7c0000000 0x086beddb7c000000 0x807fffffc0000007 0xb807fffffc000000

def z889 : W := mkw 0xcffeddb7f1a38000 0x0cffeddb7f1a3800 0xeffffffff9c7c00f 0xfeffffffff9c7c00

def z890 : W := mkw 0x009500c104c50840 0x8009500c104c5084 0x51b011c307c718c8 0x551b011c307c718c

def z891 : W := mkw 0xaffeddb7d80294a9 0x0affeddb7d80294a 0xcffffffff8033ff7 0xfcffffffff8033ff

def z892 : W := mkw 0x009746dd46cd2b56 0xc009746dd46cd2b5 0xf1bf1fffc7c7ffff 0xff1bf1fffc7c7fff

def z893 : W := mkw 0x26281802980294a9 0x026281802980294a 0x7fb81807ffc7ffff 0xf7fb81807ffc7fff

def z894 : W := mkw 0x0095024006c52804 0x00095024006c5280 0xd1b717c707c739cf 0x7d1b717c707c739c

def z895 : W := mkw 0x1b401b6823682a06 0x01b401b6823682a0 0xffc01ff83ff8000d 0xfffc01ff83ff8000

def z896 : W := mkw 0x49d5a00025b54000 0x049d5a00025b5400 0x7ff7e0003fff000b 0xe7ff7e0003fff000

def z897 : W := mkw 0x194003682b683e0e 0x0194003682b683e0 0xffc007f83ff83e09 0xeffc007f83ff83e0

def z898 : W := mkw 0x89d6c5b540000000 0x089d6c5b54000000 0x81cfeff8c0000001 0x881cfeff8c000000

def z899 : W := mkw 0xcffeddb7d0838000 0x0cffeddb7d083800 0x8fffffffc0030007 0xf8fffffffc003000

def z900 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7fffe0003ffff9cb 0xe7fffe0003ffff9c

def z901 : W := mkw 0xaffeddb7c80014a9 0x0affeddb7c80014a 0xeffffffff8003fff 0xfeffffffff8003ff

def z902 : W := mkw 0x4dfca0003132c000 0x04dfca0003132c00 0x7fffe0003ff8c00b 0xe7fffe0003ff8c00

def z903 : W := mkw 0x009766dd46dd6b56 0xc009766dd46dd6b5 0xf1fff7ff07fff9cf 0xff1fff7ff07fff9c

def z904 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8ffff7ffc0000003 0x58ffff7ffc000000

def z905 : W := mkw 0x8bd6ddb7c0000000 0x08bd6ddb7c000000 0x81c7eff8c0000001 0x081c7eff8c000000

def z906 : W := mkw 0x009706cd06cd2b46 0x8009706cd06cd2b4 0xf1b717c707ff3fcf 0x7f1b717c707ff3fc

def z907 : W := mkw 0x8ffeddb7d8029408 0x08ffeddb7d802940 0xeffffffff807fe0f 0xfeffffffff807fe0

def z908 : W := mkw 0x22025edfca483fff 0xc22025edfca483ff 0x80001fffc0003ff4 0x180001fffc0003ff

def z909 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8fffffffc004210f 0xf8fffffffc004210

def z910 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xbfc00ff83ff8260d 0xabfc00ff83ff8260

def z911 : W := mkw 0x009606c502402804 0x0009606c50240280 0xd1b717c707c739cf 0x7d1b717c707c739c

def z912 : W := mkw 0x86beddb7c0000000 0x086beddb7c000000 0x8e3fffffc0000006 0xf8e3fffffc000000

def z913 : W := mkw 0xa62a5db7d80294a9 0x0a62a5db7d80294a 0xee7ffffff807ffff 0xfee7ffffff807fff

def z914 : W := mkw 0x500122482ffd7e0e 0x0500122482ffd7e0 0x700000003ff83e08 0x0700000003ff83e0

def z915 : W := mkw 0x3b401b6aab683eaf 0x03b401b6aab683ea 0xffc01ffb3ff83ecd 0xfffc01ffb3ff83ec

def z916 : W := mkw 0x1940036823682a06 0x01940036823682a0 0xffc017f83ff8380d 0xfffc017f83ff8380

def z917 : W := mkw 0x8096c5b540000000 0x08096c5b54000000 0x8007e7f800000000 0x08007e7f80000000

def z918 : W := mkw 0xaffeddb7d80294a9 0x0affeddb7d80294a 0xaffffffff804e73f 0xfaffffffff804e73

def z919 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xfff01ff83fff3e0f 0xffff01ff83fff3e0

def z920 : W := mkw 0x89d6c5b540000000 0x089d6c5b54000000 0x81c7f7f800000005 0x781c7f7f80000000

def z921 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0xcfffffffc007000f 0xfcfffffffc007000

def z922 : W := mkw 0x4d69a0003536c000 0x04d69a0003536c00 0x7fcfe0003ffcc00b 0xe7fcfe0003ffcc00

def z923 : W := mkw 0x009500c104c50840 0x8009500c104c5084 0x51b711c707c739cf 0x751b711c707c739c

def z924 : W := mkw 0x009746d546c52944 0x8009746d546c5294 0xf1ffffffc7c7ffff 0xff1ffffffc7c7fff

def z925 : W := mkw 0x8ffeddb7c8001408 0x08ffeddb7c800140 0xeffffffff8073fcf 0xfeffffffff8073fc

def z926 : W := mkw 0x009764d544d54950 0xc009764d544d5495 0x41bff1c7c1c7d9f2 0x541bff1c7c1c7d9f

def z927 : W := mkw 0x44bfe4955497c150 0xc44bfe4955497c15 0x003fe007c007c1f2 0x0003fe007c007c1f

def z928 : W := mkw 0x009604c500c10840 0x8009604c500c1084 0xc1b017c701c318c4 0x5c1b017c701c318c

def z929 : W := mkw 0x3f681b2abb2ab6af 0x03f681b2abb2ab6a 0xbe480e3cfe3ce73f 0xabe480e3cfe3ce73

def z930 : W := mkw 0x26281802980294a9 0x026281802980294a 0x2e381807f807fff6 0x92e381807f807fff

def z931 : W := mkw 0x1dfc82482b683e0e 0x01dfc82482b683e0 0x7fffe0003ff83e0b 0xe7fffe0003ff83e0

def z932 : W := mkw 0x0003665c46dd6b56 0xc0003665c46dd6b5 0xf1cffffcc7ffffff 0xff1cffffcc7fffff

def z933 : W := mkw 0x100122482ffd7f5e 0xc100122482ffd7f5 0x700000003ffffff8 0x0700000003ffffff

def z934 : W := mkw 0x009646dd42c92b56 0xc009646dd42c92b5 0xc1b01fffc1c33ff4 0x5c1b01fffc1c33ff

def z935 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xfff01ffb3ffb3ecd 0xffff01ffb3ffb3ec

def z936 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8ff7ffffc0000005 0x58ff7ffffc000000

def z937 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8ffff7fb00000003 0xf8ffff7fb0000000

def z938 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7ffff807ffffffff 0xf7ffff807fffffff

def z939 : W := mkw 0x7f68b92ab93ad6ab 0x07f68b92ab93ad6a 0x2e48e838f838c630 0x82e48e838f838c63

def z940 : W := mkw 0x89d6c5b540000000 0x089d6c5b54000000 0x8fc7e7f800000001 0xe8fc7e7f80000000

def z941 : W := mkw 0x009400c100c10840 0x8009400c100c1084 0x61b819c7c1c7fffe 0xf61b819c7c1c7fff

def z942 : W := mkw 0x0000024002402804 0x0000002400240280 0xd1b017c307c338cd 0x7d1b017c307c338c

def z943 : W := mkw 0x8dfec5b7c0000000 0x08dfec5b7c000000 0x81cfe7f8c0000001 0x081cfe7f8c000000

def z944 : W := mkw 0x4d6aa6c53372e944 0x84d6aa6c53372e94 0xae48f7c73838f9c4 0x9ae48f7c73838f9c

def z945 : W := mkw 0xaffeddb7d80294a9 0x0affeddb7d80294a 0xaffffffff800fff7 0xfaffffffff800fff

def z946 : W := mkw 0xaffeddb7c80014a9 0x0affeddb7c80014a 0x8fffffffc00018c7 0xf8fffffffc00018c

def z947 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7ff7e0003fffc009 0x47ff7e0003fffc00

def z948 : W := mkw 0x92025ffd4a483e0e 0x092025ffd4a483e0 0x80001ff800003e04 0x180001ff800003e0

def z949 : W := mkw 0x0200180008001408 0x0020018000800140 0x6e381807f807fffe 0xf6e381807f807fff

def z950 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xf1b717c707c7ffff 0x7f1b717c707c7fff

def z951 : W := mkw 0x0b401b2823282206 0x00b401b282328220 0xffc01ff83ff8260d 0xfffc01ff83ff8260

def z952 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0xdfffffffc7c0000f 0xfdfffffffc7c0000

def z953 : W := mkw 0x0001224806dd6b56 0xc0001224806dd6b5 0x70381807c7fffffe 0xf70381807c7fffff

def z954 : W := mkw 0x0003669d461c6316 0x40003669d461c631 0xb04fffffc63ce73f 0xbb04fffffc63ce73

def z955 : W := mkw 0x0002661c42186216 0x40002661c4218621 0xb04fee3cc638e63f 0xab04fee3cc638e63

def z956 : W := mkw 0x009704c504c50940 0x8009704c504c5094 0x51b711c707c719cb 0x751b711c707c719c

def z957 : W := mkw 0x8dfec5b7c0000000 0x08dfec5b7c000000 0x81ffefffc0000007 0xa81ffefffc000000

def z958 : W := mkw 0xb2025fffca483eaf 0x0b2025fffca483ea 0x80001fffc0003ff4 0x180001fffc0003ff

def z959 : W := mkw 0x500122483fffff1e 0x4500122483fffff1 0x700000003fffff38 0x0700000003fffff3

def z960 : W := mkw 0x49d5a00025b54000 0x049d5a00025b5400 0x5fc7e0003ff80001 0x45fc7e0003ff8000

def z961 : W := mkw 0x0002449540000000 0x0000244954000000 0x804fffffc0000007 0xb804fffffc000000

def z962 : W := mkw 0xaffeddb7c00000a1 0x0affeddb7c00000a 0x8fffffffc00001f7 0xf8fffffffc00001f

def z963 : W := mkw 0x00016218461c6316 0x400016218461c631 0x304fe838c63ce73b 0xa304fe838c63ce73

def z964 : W := mkw 0x009402c102c12844 0x8009402c102c1284 0xc1b017c301c338c4 0x5c1b017c301c338c

def z965 : W := mkw 0x09d5200025b54000 0x009d5200025b5400 0x7fffe0003fffc00b 0xe7fffe0003fffc00

def z966 : W := mkw 0x0003641444144000 0x0000364144414400 0xb04fee3cc63ce73f 0xab04fee3cc63ce73

def z967 : W := mkw 0x0b40192000000000 0x00b4019200000000 0x8fcffff800000007 0xf8fcffff80000000

def z968 : W := mkw 0xcffeddb7e1a10000 0x0cffeddb7e1a1000 0x8fffffffc1c00007 0xf8fffffffc1c0000

def z969 : W := mkw 0x5001224837ffea06 0x05001224837ffea0 0x700000003fffc008 0x0700000003fffc00

def z970 : W := mkw 0x100122482f7c7f1e 0x4100122482f7c7f1 0x700000003ff83e08 0x0700000003ff83e0

def z971 : W := mkw 0x04bd20001497c000 0x004bd20001497c00 0x7fffe0003fffc00b 0xe7fffe0003fffc00

def z972 : W := mkw 0x89d6c5b540000000 0x089d6c5b54000000 0x81ffffffc0000007 0xf81ffffffc000000

def z973 : W := mkw 0x0003064406442904 0x0000306440644290 0xd1b717c707c739cf 0x7d1b717c707c739c

def z974 : W := mkw 0x009766dd46dd6b56 0xc009766dd46dd6b5 0xf1bff7c7c7ffffff 0x7f1bff7c7c7fffff

def z975 : W := mkw 0x009402c102c12844 0x8009402c102c1284 0x51b011c307c338c8 0x551b011c307c338c

def z976 : W := mkw 0x0001224806dd6b56 0xc0001224806dd6b5 0x5000000007ff39c8 0x05000000007ff39c

def z977 : W := mkw 0xc9d6c5b561a10000 0x0c9d6c5b561a1000 0x81c7e7f801c00001 0x081c7e7f801c0000

def z978 : W := mkw 0x8bd6ddb7c0000000 0x08bd6ddb7c000000 0x81f7ffffc0000007 0x781f7ffffc000000

def z979 : W := mkw 0x009766dd46dd6b56 0xc009766dd46dd6b5 0xd1f7ffffc7ff3fff 0x7d1f7ffffc7ff3ff

def z980 : W := mkw 0x00016018441c4212 0x400016018441c421 0x304fe838c638c631 0x8304fe838c638c63

def z981 : W := mkw 0x200122481edfffff 0xc200122481edffff 0x700000003ffffff8 0x0700000003ffffff

def z982 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xf04fee3cc63fffff 0xaf04fee3cc63ffff

def z983 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xb04fee38c63cc63b 0xab04fee38c63cc63

def z984 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xb04fee38c63ce739 0x8b04fee38c63ce73

def z985 : W := mkw 0x8ffeddb7c8001408 0x08ffeddb7c800140 0x8fffffffc0003e07 0xf8fffffffc0003e0

def z986 : W := mkw 0x26281802980294a9 0x026281802980294a 0x7e781807fe3fffff 0xf7e781807fe3ffff

def z987 : W := mkw 0x3f68793af93ad6bb 0x43f68793af93ad6b 0x2e48e838f838c630 0x82e48e838f838c63

def z988 : W := mkw 0x1b4019282928160a 0x01b4019282928160 0xffc01ff83ff8060d 0xfffc01ff83ff8060

def z989 : W := mkw 0xaffeddb7d80294a9 0x0affeddb7d80294a 0x8ffffffff8000007 0xf8ffffffff800000

def z990 : W := mkw 0x009502c106c52944 0x8009502c106c5294 0x51b711c307c739cb 0x751b711c307c739c

def z991 : W := mkw 0x8ffeddb540000000 0x08ffeddb54000000 0x8ffffff800000007 0xf8ffffff80000000

def z992 : W := mkw 0x8b425db7c0000000 0x08b425db7c000000 0x8fcfffffc0000007 0xf8fcfffffc000000

def z993 : W := mkw 0x4dfc800031a38000 0x04dfc800031a3800 0x7fffe0003ffb000b 0xe7fffe0003ffb000

def z994 : W := mkw 0x10012248277c6b16 0x410012248277c6b1 0x1000000007f80000 0x01000000007f8000

def z995 : W := mkw 0x009706cd06cd2b46 0x8009706cd06cd2b4 0xf1ff1fffc7ffffff 0xff1ff1fffc7fffff

def z996 : W := mkw 0x009606c502c12944 0x8009606c502c1294 0xc1b017c301c318c0 0x5c1b017c301c318c

def z997 : W := mkw 0xaffeddb7f92294a9 0x0affeddb7f92294a 0xffffffffffffffff 0xffffffffffffffff

def z998 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7ffff0033fffd8cb 0xf7ffff0033fffd8c

def z999 : W := mkw 0x8ffeddb7d0028000 0x08ffeddb7d002800 0xeffffffff807e73f 0xfeffffffff807e73

def z1000 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8fffffffc0002737 0xf8fffffffc000273

def z1001 : W := mkw 0x2ffc9922980294a9 0x02ffc9922980294a 0xeffffffff807ffff 0xfeffffffff807fff

def z1002 : W := mkw 0x00012248065c6b56 0xc00012248065c6b5 0x30000000063cfff8 0x030000000063cfff

def z1003 : W := mkw 0x0b425d3448001408 0x00b425d344800140 0xefcffffcf804ff3f 0xfefcffffcf804ff3

def z1004 : W := mkw 0x4dfda00025b54000 0x04dfda00025b5400 0x7fffe0003ff8000b 0xe7fffe0003ff8000

def z1005 : W := mkw 0xc4bfe497d497c140 0x8c4bfe497d497c14 0x003fe007c007c1c2 0x0003fe007c007c1c

def z1006 : W := mkw 0x49d7e6dd67fd6b56 0xc49d7e6dd67fd6b5 0x91c7e7f807f80001 0x091c7e7f807f8000

def z1007 : W := mkw 0x00012248065c6b16 0x400012248065c6b1 0x7000000007fcff38 0x07000000007fcff3

def z1008 : W := mkw 0x84bec5b7c0000000 0x084bec5b7c000000 0x803fe7ffc0000002 0x0803fe7ffc000000

def z1009 : W := mkw 0x8ffc99a380000000 0x08ffc99a38000000 0x8ffffffb00000007 0xf8ffffffb0000000

def z1010 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x1fc7e0003ff80001 0x01fc7e0003ff8000

def z1011 : W := mkw 0x8dfec5b7c0000000 0x08dfec5b7c000000 0x81fff7ffc0000007 0x781fff7ffc000000

def z1012 : W := mkw 0x009704c504c50940 0x8009704c504c5094 0xc1b717c701c719c7 0x7c1b717c701c719c

def z1013 : W := mkw 0xbf68d93af92a96ab 0x0bf68d93af92a96a 0x2e48e838f838c630 0x82e48e838f838c63

def z1014 : W := mkw 0xaffeddb7d00280a1 0x0affeddb7d00280a 0x8fffffffc000c037 0xf8fffffffc000c03

def z1015 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xf1bf17c707c7f9cf 0xff1bf17c707c7f9c

def z1016 : W := mkw 0x009606c502c12944 0x8009606c502c1294 0xc1b717c701c339c7 0x7c1b717c701c339c

def z1017 : W := mkw 0x009402c102c12844 0x8009402c102c1284 0xd1b017c307c318c1 0x5d1b017c307c318c

def z1018 : W := mkw 0x009766d546d56954 0xc009766d546d5695 0xf1fff7c7c7fff9ff 0xff1fff7c7c7fff9f

def z1019 : W := mkw 0xcdfda1a135b7c000 0x0cdfda1a135b7c00 0x7fffe1c03fffc00b 0xe7fffe1c03fffc00

def z1020 : W := mkw 0x89d6c5b540000000 0x089d6c5b54000000 0xa1cfeffcc004e73f 0xaa1cfeffcc004e73

def z1021 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7e7fe0003fffc00a 0x87e7fe0003fffc00

def z1022 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xb04fee3cc638e735 0x8b04fee3cc638e73

def z1023 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xb04fee3cc638c637 0xab04fee3cc638c63

def z1024 : W := mkw 0x009766dd46dd6b56 0xc009766dd46dd6b5 0xd1f7f7fb07fb18c1 0x5d1f7f7fb07fb18c

def z1025 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xd1f71fff07c739cf 0xfd1f71fff07c739c

def z1026 : W := mkw 0x0ffc992280000000 0x00ffc99228000000 0x8fffffffc0000007 0xf8fffffffc000000

def z1027 : W := mkw 0xc4bfe4955497c000 0x0c4bfe4955497c00 0x003fe0000007c002 0x0003fe0000007c00

def z1028 : W := mkw 0x84bec497c0000000 0x084bec497c000000 0x81ffffffc0000007 0xf81ffffffc000000

def z1029 : W := mkw 0x6dfda00035b7c0a1 0x06dfda00035b7c0a 0x7fffe0003fffc1fb 0xe7fffe0003fffc1f

def z1030 : W := mkw 0x0940000021200000 0x0094000002120000 0x7fcfe0003ff8000b 0xe7fcfe0003ff8000

def z1031 : W := mkw 0x009502c106c52944 0x8009502c106c5294 0x51b011c307c318c0 0x551b011c307c318c

def z1032 : W := mkw 0xaffeddb7d80294a9 0x0affeddb7d80294a 0xeffffffff803def7 0xfeffffffff803def

def z1033 : W := mkw 0x8ffeddb7c8001408 0x08ffeddb7c800140 0xcffffffff8001807 0xfcffffffff800180

def z1034 : W := mkw 0x8dfec5b7c0000000 0x08dfec5b7c000000 0x8fffe7ffc0000003 0xe8fffe7ffc000000

def z1035 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8fcfffffc0000005 0x98fcfffffc000000

def z1036 : W := mkw 0xe4bfe497d497c0a1 0x0e4bfe497d497c0a 0x003fe007c007c1f2 0x0003fe007c007c1f

def z1037 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7fffe8003fffe60f 0xe7fffe8003fffe60

def z1038 : W := mkw 0x06be5c97c0000000 0x006be5c97c000000 0x8fffffffc0000007 0xf8fffffffc000000

def z1039 : W := mkw 0x000366dd46dd6b56 0xc000366dd46dd6b5 0xf04fffffc7ffffff 0xbf04fffffc7fffff

def z1040 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8ff7fffb00000005 0xf8ff7fffb0000000

def z1041 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xf04ffe3cc63cff3f 0xff04ffe3cc63cff3

def z1042 : W := mkw 0x8ffeddb7d0028000 0x08ffeddb7d002800 0x8fffffffc007c007 0xf8fffffffc007c00

def z1043 : W := mkw 0x500122483fffff4e 0x8500122483fffff4 0x700000003fffffc8 0x0700000003fffffc

def z1044 : W := mkw 0x0003661c469d6316 0x40003661c469d631 0xf04fee3cc7ffe73f 0xaf04fee3cc7ffe73

def z1045 : W := mkw 0x0001224806dd6b56 0xc0001224806dd6b5 0x1000000007f80000 0x01000000007f8000

def z1046 : W := mkw 0x3b401b6aab683eaf 0x03b401b6aab683ea 0xffc81ffffffcffff 0xfffc81ffffffcfff

def z1047 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0xafffffffc004c00f 0xfafffffffc004c00

def z1048 : W := mkw 0x5001224827fd6a06 0x05001224827fd6a0 0x1000000007f80000 0x01000000007f8000

def z1049 : W := mkw 0x009766dd46dd6b56 0xc009766dd46dd6b5 0xd1ffffffc7ff39cf 0xfd1ffffffc7ff39c

def z1050 : W := mkw 0x009706cd06cd2b46 0x8009706cd06cd2b4 0xd1b71fff07c73fcf 0x7d1b71fff07c73fc

def z1051 : W := mkw 0xbffc99e3b9629ca9 0x0bffc99e3b9629ca 0x4fb011c339c318c0 0x54fb011c339c318c

def z1052 : W := mkw 0x82025db7c0000000 0x082025db7c000000 0x8047ffffc0000005 0x18047ffffc000000

def z1053 : W := mkw 0x24bf6497d497c1f1 0xc24bf6497d497c1f 0x003fe007c007c1f2 0x0003fe007c007c1f

def z1054 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8fffffffc00701c7 0xf8fffffffc00701c

def z1055 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xfff01fff3ff83e0f 0xffff01fff3ff83e0

def z1056 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x5fffe0003ffb0003 0xe5fffe0003ffb000

def z1057 : W := mkw 0x12025f7c4a483e0e 0x012025f7c4a483e0 0x80001ffcc0003e04 0x180001ffcc0003e0

def z1058 : W := mkw 0x0001224806dd6b56 0xc0001224806dd6b5 0x3000000007fce738 0x03000000007fce73

def z1059 : W := mkw 0x000366dd465c6b56 0xc000366dd465c6b5 0xb04feffcc63ce73f 0xab04feffcc63ce73

def z1060 : W := mkw 0x8dfec5b7c0000000 0x08dfec5b7c000000 0x81f7e7fb00000001 0x081f7e7fb0000000

def z1061 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0x91b717c707c739c7 0x191b717c707c739c

def z1062 : W := mkw 0x26281802980294a9 0x026281802980294a 0xee781e3ff807ffff 0xfee781e3ff807fff

def z1063 : W := mkw 0x86beddb7c0000000 0x086beddb7c000000 0x81bfffffc0000007 0x781bfffffc000000

def z1064 : W := mkw 0xcdfda083b5b7c000 0x0cdfda083b5b7c00 0x7fffe0033fffc00b 0xe7fffe0033fffc00

def z1065 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xffc01ff83ffcff3d 0xfffc01ff83ffcff3

def z1066 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7fffe800ffffc63b 0xe7fffe800ffffc63

def z1067 : W := mkw 0xaffeddb7d80294a9 0x0affeddb7d80294a 0xeffffffff8033ecf 0xfeffffffff8033ec

def z1068 : W := mkw 0x49d5a00025b54000 0x049d5a00025b5400 0x3fc7e0003ff80001 0x83fc7e0003ff8000

def z1069 : W := mkw 0x009726cd06dd6b56 0xc009726cd06dd6b5 0xd1b717c707ff39cf 0x7d1b717c707ff39c

def z1070 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xffc01ffcfff83f3d 0xfffc01ffcfff83f3

def z1071 : W := mkw 0x8bd6ddb7c0000000 0x08bd6ddb7c000000 0x81cfffffc0000007 0xb81cfffffc000000

def z1072 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8ffffffbc0000001 0xd8ffffffbc000000

def z1073 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xd1b017c707c739cc 0x5d1b017c707c739c

def z1074 : W := mkw 0x009746d546c52944 0x8009746d546c5294 0xd1f7f7ff07c739cf 0x7d1f7f7ff07c739c

def z1075 : W := mkw 0x009766d546d56954 0xc009766d546d5695 0xd1b7f7c707c739cf 0x7d1b7f7c707c739c

def z1076 : W := mkw 0x000366dd465c6b56 0xc000366dd465c6b5 0xf07fffffc63fffff 0xff07fffffc63ffff

def z1077 : W := mkw 0x8ffeddb7d0028000 0x08ffeddb7d002800 0xeffffffff807f9cf 0xfeffffffff807f9c

def z1078 : W := mkw 0x8dfec5b540000000 0x08dfec5b54000000 0x81ffe7f800000003 0x081ffe7f80000000

def z1079 : W := mkw 0x0942453440000000 0x0094245344000000 0x81cfeffcc0000007 0xa81cfeffcc000000

def z1080 : W := mkw 0x4dfda002b5b7c000 0x04dfda002b5b7c00 0x7fffe007ffffc00b 0xe7fffe007ffffc00

def z1081 : W := mkw 0xa6beddb7d80294a9 0x0a6beddb7d80294a 0xee3ffffff807fffe 0xfee3ffffff807fff

def z1082 : W := mkw 0x009766d546d56954 0xc009766d546d5695 0xd1ffffffc7c7f9ff 0xfd1ffffffc7c7f9f

def z1083 : W := mkw 0x009520c104d54840 0x8009520c104d5484 0x71fff1c307ffd8cb 0xf71fff1c307ffd8c

def z1084 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xffc81ff83ffcfe0f 0xfffc81ff83ffcfe0

def z1085 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xf07fee3cc63fe73f 0xef07fee3cc63fe73

def z1086 : W := mkw 0x09d4812000000000 0x009d481200000000 0x81c7e7f800000001 0x081c7e7f80000000

def z1087 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xd1b71fc7c7c73fff 0x7d1b71fc7c7c73ff

def z1088 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xffc81ffcfff83e0f 0xfffc81ffcfff83e0

def z1089 : W := mkw 0x0003661c469d6356 0xc0003661c469d635 0xb04fee3cc63fe7ff 0xab04fee3cc63fe7f

def z1090 : W := mkw 0x4dfda00035b7c140 0x84dfda00035b7c14 0x7fffe0003fffc1cb 0xe7fffe0003fffc1c

def z1091 : W := mkw 0x8dfec5b550028000 0x08dfec5b55002800 0xefffe7f83807c00b 0xeefffe7f83807c00

def z1092 : W := mkw 0x009726c506d56944 0x8009726c506d5694 0xd1f7f7c707ff39cf 0x7d1f7f7c707ff39c

def z1093 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0xcfffffffc000380f 0xfcfffffffc000380

def z1094 : W := mkw 0x8ffeddb7c0810000 0x08ffeddb7c081000 0xcfffffffc1c30007 0xfcfffffffc1c3000

def z1095 : W := mkw 0x0f6a5d36c0000000 0x00f6a5d36c000000 0x8fffffffc0000007 0xf8fffffffc000000

def z1096 : W := mkw 0x009400c100c10840 0x8009400c100c1084 0x41b011c301c338cc 0x741b011c301c338c

def z1097 : W := mkw 0x009726cd06dd6b56 0xc009726cd06dd6b5 0xf1fff7c707ffffff 0xff1fff7c707fffff

def z1098 : W := mkw 0x009604c500c10840 0x8009604c500c1084 0xc1b717c301c318c1 0x5c1b717c301c318c

def z1099 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x3fffe0003ff8c003 0xe3fffe0003ff8c00

def z1100 : W := mkw 0x49d5a00035b7c000 0x049d5a00035b7c00 0x7fc7e0003fffc009 0xe7fc7e0003fffc00

def z1101 : W := mkw 0x09d4800021200000 0x009d480002120000 0x7fc7e0003ff80009 0xe7fc7e0003ff8000

def z1102 : W := mkw 0x89d6c5b540000000 0x089d6c5b54000000 0x81c7f7ff00000005 0x181c7f7ff0000000

def z1103 : W := mkw 0x0002641c40184212 0x40002641c4018421 0x204fe83cc038c632 0x8204fe83cc038c63

def z1104 : W := mkw 0x009726c506d56954 0xc009726c506d5695 0xd1b717c707c7f9ff 0x7d1b717c707c7f9f

def z1105 : W := mkw 0x0bd4992000000000 0x00bd499200000000 0x8fc7fff800000005 0xf8fc7fff80000000

def z1106 : W := mkw 0x4dfda08135b7c000 0x04dfda08135b7c00 0x7ffff1c33fffc00b 0xf7ffff1c33fffc00

def z1107 : W := mkw 0x00016218461c6216 0x400016218461c621 0xb04fee38c63ce63f 0xab04fee38c63ce63

def z1108 : W := mkw 0x009766dd46dd6b56 0xc009766dd46dd6b5 0xd1bfffffc7c7ffff 0x7d1bfffffc7c7fff

def z1109 : W := mkw 0x0b425d3440000000 0x00b425d344000000 0x8fc7fff800000005 0xf8fc7fff80000000

def z1110 : W := mkw 0x009746dd46cd2b56 0xc009746dd46cd2b5 0xd1b717ff07c739cf 0x7d1b717ff07c739c

def z1111 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xffb717c73fc739cf 0xfffb717c73fc739c

def z1112 : W := mkw 0x300122483f7effbf 0x4300122483f7effb 0x700000003ffffff8 0x0700000003ffffff

def z1113 : W := mkw 0xaffeddb7d00280a1 0x0affeddb7d00280a 0x8fffffffc00300c7 0xf8fffffffc00300c

def z1114 : W := mkw 0x3f681922b92294a9 0x03f681922b92294a 0x0e00000038000000 0x00e0000003800000

def z1115 : W := mkw 0x0003665c465c6b16 0x40003665c465c6b1 0xb1cfeffcc7fce73f 0xab1cfeffcc7fce73

def z1116 : W := mkw 0x7ffc9962b9e39ca9 0x07ffc9962b9e39ca 0x4fb011c339c318c0 0x54fb011c339c318c

def z1117 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0xafffffffc000c637 0xfafffffffc000c63

def z1118 : W := mkw 0x4429200035b7c000 0x04429200035b7c00 0x7e7fe0003fffc00b 0xe7e7fe0003fffc00

def z1119 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xfe4fee3cfe3ce73f 0xefe4fee3cfe3ce73

def z1120 : W := mkw 0xeffeddb7f9a394a9 0x0effeddb7f9a394a 0xeffffffff9c7ffff 0xfeffffffff9c7fff

def z1121 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xffc01ff83fff3fcd 0xfffc01ff83fff3fc

def z1122 : W := mkw 0x009400c100c10840 0x8009400c100c1084 0xc1b017c301c318c5 0x7c1b017c301c318c

def z1123 : W := mkw 0x009766dd46dd6b56 0xc009766dd46dd6b5 0xf1b71fffc7ffffff 0x7f1b71fffc7fffff

def z1124 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xffc01ff83ff81e01 0xdffc01ff83ff81e0

def z1125 : W := mkw 0x0b401b6023602804 0x00b401b602360280 0xffc01ff83ff8380d 0xfffc01ff83ff8380

def z1126 : W := mkw 0x3b401b682b683eaf 0x03b401b682b683ea 0xffc01ff83ff83ffd 0xfffc01ff83ff83ff

def z1127 : W := mkw 0x8dfec5b540000000 0x08dfec5b54000000 0x8fffeffcc0000007 0xe8fffeffcc000000

def z1128 : W := mkw 0x0002641c40184212 0x40002641c4018421 0xa04fee3cc03ce73f 0xaa04fee3cc03ce73

def z1129 : W := mkw 0x8296ddb7c0000000 0x08296ddb7c000000 0x8007ffffc0000004 0x18007ffffc000000

def z1130 : W := mkw 0x8ffeddb7e1200000 0x08ffeddb7e120000 0xaffffffff8380007 0xfaffffffff838000

def z1131 : W := mkw 0x009400c100c10840 0x8009400c100c1084 0x41b011c301c718ca 0x741b011c301c718c

def z1132 : W := mkw 0x1b401b6aab683e0e 0x01b401b6aab683e0 0xffc01ffffff83e0d 0xfffc01ffffff83e0

def z1133 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xffc017f83ff81809 0xfffc017f83ff8180

def z1134 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8fffffffc00039c7 0xf8fffffffc00039c

def z1135 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xd1bf1fc7c7c739cf 0xfd1bf1fc7c7c739c

def z1136 : W := mkw 0x009400c100c10840 0x8009400c100c1084 0x51b011c307c318c9 0x751b011c307c318c

def z1137 : W := mkw 0x009726c506d56944 0x8009726c506d5694 0xd1bff7c707c7f9cf 0x7d1bff7c707c7f9c

def z1138 : W := mkw 0x009704c504c50840 0x8009704c504c5084 0xd1b717c707c718cf 0x7d1b717c707c718c

def z1139 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7fffe0003ffbc001 0xc7fffe0003ffbc00

def z1140 : W := mkw 0x02025d3440000000 0x002025d344000000 0x804ffffcc0000007 0xb804ffffcc000000

def z1141 : W := mkw 0x0d6920003536c000 0x00d6920003536c00 0x7fffe0003fffc00b 0xe7fffe0003fffc00

def z1142 : W := mkw 0x0942453440000000 0x0094245344000000 0x81c7e7f800000001 0x081c7e7f80000000

def z1143 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0xafffffffc000260f 0xfafffffffc000260

def z1144 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xd1b717c307c338cd 0x7d1b717c307c338c

def z1145 : W := mkw 0x6dfda002b5b7c0a1 0x06dfda002b5b7c0a 0x7ffff007fffff9ff 0xf7ffff007fffff9f

def z1146 : W := mkw 0x0000004000400800 0x0000000400040080 0x41b011c301c318c0 0x541b011c301c318c

def z1147 : W := mkw 0x0003641c441c4312 0x40003641c441c431 0x304fe83cc63cc73b 0xa304fe83cc63cc73

def z1148 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x5fffe0003fffc003 0x45fffe0003fffc00

def z1149 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xffc017f83ff83e09 0x5ffc017f83ff83e0

def z1150 : W := mkw 0x8ffeddb7c8001408 0x08ffeddb7c800140 0xaffffffff8000607 0xfaffffffff800060

def z1151 : W := mkw 0xaffeddb7c80014a9 0x0affeddb7c80014a 0xcfffffffc0073fff 0xfcfffffffc0073ff

def z1152 : W := mkw 0xadfec5b7d00280a1 0x0adfec5b7d00280a 0x81ffe7ffc007c1f3 0x081ffe7ffc007c1f

def z1153 : W := mkw 0x26281802980294a9 0x026281802980294a 0x4e381807f807fff6 0x54e381807f807fff

def z1154 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xbfc01ff83ff83e05 0x9bfc01ff83ff83e0

def z1155 : W := mkw 0x8bd6ddb7c0000000 0x08bd6ddb7c000000 0x81c7f7fb00000001 0x181c7f7fb0000000

def z1156 : W := mkw 0x009400c100c10840 0x8009400c100c1084 0x41b011c301c739c8 0x541b011c301c739c

def z1157 : W := mkw 0x0ffedd3440000000 0x00ffedd344000000 0x8ffffffcc0000007 0xf8ffffffcc000000

def z1158 : W := mkw 0x009704c504c50940 0x8009704c504c5094 0x41b711c301c318c0 0x541b711c301c318c

def z1159 : W := mkw 0x1b40196029601c08 0x01b40196029601c0 0xffc01ff83ff8180d 0xfffc01ff83ff8180

def z1160 : W := mkw 0xcdfec5b571a38000 0x0cdfec5b571a3800 0xcff7e7f839c30001 0x4cff7e7f839c3000

def z1161 : W := mkw 0x4097a6c506d56944 0x84097a6c506d5694 0xd1b7f7c707c739cf 0x7d1b7f7c707c739c

def z1162 : W := mkw 0x26281802980294a9 0x026281802980294a 0x6e301807f807fffc 0x56e301807f807fff

def z1163 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0x904fee3cc63ce737 0x0904fee3cc63ce73

def z1164 : W := mkw 0xa6beddb7d80294a9 0x0a6beddb7d80294a 0x803fffffc007fff6 0x1803fffffc007fff

def z1165 : W := mkw 0x009502c106c52844 0x8009502c106c5284 0xd1b717c307c738cf 0x7d1b717c307c738c

def z1166 : W := mkw 0xaffeddb7d80294a9 0x0affeddb7d80294a 0xafcfeff8f800c631 0x8afcfeff8f800c63

def z1167 : W := mkw 0x800245b540000000 0x0800245b54000000 0x804feffcc0000007 0xa804feffcc000000

def z1168 : W := mkw 0x8bd6ddb540000000 0x08bd6ddb54000000 0x8fcffffcc0000007 0xf8fcffffcc000000

def z1169 : W := mkw 0x3f6b7f3eff3ef7bf 0x43f6b7f3eff3ef7b 0xbe4fee3cfe3ce73f 0xabe4fee3cfe3ce73

def z1170 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7fffe0043fffe10f 0xe7fffe0043fffe10

def z1171 : W := mkw 0x0940012021200000 0x0094001202120000 0xffc007f83ff80009 0xeffc007f83ff8000

def z1172 : W := mkw 0x1940036823682a06 0x01940036823682a0 0xffc00ff83ff8260d 0xeffc00ff83ff8260

def z1173 : W := mkw 0x8ffcd932c0000000 0x08ffcd932c000000 0x8ffffff8c0000007 0xf8ffffff8c000000

def z1174 : W := mkw 0x009500c104c50840 0x8009500c104c5084 0x41b711c301c718c2 0x541b711c301c718c

def z1175 : W := mkw 0x8ffeddb7d0028000 0x08ffeddb7d002800 0xcffffffff8030007 0xfcffffffff803000

def z1176 : W := mkw 0x009706cd06cd2b46 0x8009706cd06cd2b4 0xd1f717ff07ff39cf 0x7d1f717ff07ff39c

def z1177 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7fcfe0003ff8c009 0xe7fcfe0003ff8c00

def z1178 : W := mkw 0x009500c104c50840 0x8009500c104c5084 0x51b711c307c318c1 0x551b711c307c318c

def z1179 : W := mkw 0x26281802980294a9 0x026281802980294a 0x6e7ff807f807ffff 0xf6e7ff807f807fff

def z1180 : W := mkw 0x1940036823682a06 0x01940036823682a0 0xbfc007f83ff80001 0x8bfc007f83ff8000

def z1181 : W := mkw 0x10012248277c6b16 0x410012248277c6b1 0x3000000007fce738 0x03000000007fce73

def z1182 : W := mkw 0x76293a4abffffeaf 0x076293a4abffffea 0x7e381807fffffffe 0xf7e381807fffffff

def z1183 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xffcffff83ff83e0f 0xfffcffff83ff83e0

def z1184 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0xeffffffff800000f 0xfeffffffff800000

def z1185 : W := mkw 0xaffeddb7d80294a9 0x0affeddb7d80294a 0x8fffffffc007fff7 0xf8fffffffc007fff

def z1186 : W := mkw 0x3f681922b92294a9 0x03f681922b92294a 0x2e080800f800c630 0x82e080800f800c63

def z1187 : W := mkw 0xaffeddb7c80014a9 0x0affeddb7c80014a 0xafffffffc004ffff 0xfafffffffc004fff

def z1188 : W := mkw 0x700122483ffffeaf 0x0700122483ffffea 0x700000003ffffff8 0x0700000003ffffff

def z1189 : W := mkw 0x44bda00035b7c000 0x044bda00035b7c00 0x7e3fe0003fffc00a 0xe7e3fe0003fffc00

def z1190 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xd1b717c307c718cb 0x7d1b717c307c718c

def z1191 : W := mkw 0x0003641c441c4312 0x40003641c441c431 0xa04fee3cc03cc737 0xaa04fee3cc03cc73

def z1192 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8fffeff8c0000003 0xe8fffeff8c000000

def z1193 : W := mkw 0x0003641c441c4312 0x40003641c441c431 0x204fe83cc03ce73e 0xa204fe83cc03ce73

def z1194 : W := mkw 0x009400c100c10840 0x8009400c100c1084 0x41b011c701c318c6 0x741b011c701c318c

def z1195 : W := mkw 0x89d6c5b540000000 0x089d6c5b54000000 0x81f7e7f800000003 0x681f7e7f80000000

def z1196 : W := mkw 0x8bd6ddb540000000 0x08bd6ddb54000000 0x81c7fff800000005 0x181c7fff80000000

def z1197 : W := mkw 0x009746d546c52954 0xc009746d546c5295 0xd1b717c7c7c739ff 0x7d1b717c7c7c739f

def z1198 : W := mkw 0x0096449540000000 0x0009644954000000 0x81cfeffcc0000007 0xa81cfeffcc000000

def z1199 : W := mkw 0x009500c104c50940 0x8009500c104c5094 0x41b011c301c719c0 0x541b011c301c719c

def z1200 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xb07fee3fc63fe7ff 0xab07fee3fc63fe7f

def z1201 : W := mkw 0x89d6c5b540000000 0x089d6c5b54000000 0xc1f7f7ff000739cf 0x7c1f7f7ff000739c

def z1202 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7fffe004ffffc13b 0xe7fffe004ffffc13

def z1203 : W := mkw 0x009606c502c12844 0x8009606c502c1284 0xd1b717c707c338cf 0x7d1b717c707c338c

def z1204 : W := mkw 0x36293a4abf7effbf 0x436293a4abf7effb 0x7e381807fffffffe 0xf7e381807fffffff

def z1205 : W := mkw 0xcffeddb7f1a38000 0x0cffeddb7f1a3800 0xfffffffffffb000f 0xffffffffffffb000

def z1206 : W := mkw 0x8ffeddb7c0000000 0x08ffeddb7c000000 0x8e7fffffc0000006 0x98e7fffffc000000

def z1207 : W := mkw 0x56293a483ffffe0e 0x056293a483ffffe0 0x7e3818003ffffe0e 0xf7e3818003ffffe0

def z1208 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7fbfe0003fffc00a 0x47fbfe0003fffc00

def z1209 : W := mkw 0x009766d546d56944 0x8009766d546d5694 0xf1ffffffc7fff9cf 0xff1ffffffc7fff9c

def z1210 : W := mkw 0x009766dd46dd6b56 0xc009766dd46dd6b5 0xf1f7ffff07ff3fcf 0xff1f7ffff07ff3fc

def z1211 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xd1b717c307c739c9 0x5d1b717c307c739c

def z1212 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0xfffff7c03fffc00f 0xffffff7c03fffc00

def z1213 : W := mkw 0x100122482f7c7e0e 0x0100122482f7c7e0 0x700000003ffcfe08 0x0700000003ffcfe0

def z1214 : W := mkw 0x8097c6d546c52944 0x88097c6d546c5294 0xd1b7f7c707c739cf 0x7d1b7f7c707c739c

def z1215 : W := mkw 0x8bd6ddb7c0000000 0x08bd6ddb7c000000 0x8fc7ffffc0000005 0xf8fc7ffffc000000

def z1216 : W := mkw 0x009400c100c10840 0x8009400c100c1084 0x41b011c701c339c4 0x541b011c701c339c

def z1217 : W := mkw 0x0ffe9da500000000 0x00ffe9da50000000 0x8fffffff00000007 0xf8fffffff0000000

def z1218 : W := mkw 0x009604c500c10840 0x8009604c500c1084 0x41b711c701c318c2 0x541b711c701c318c

def z1219 : W := mkw 0x4dfda00035b7c110 0x44dfda00035b7c11 0x7fffe0003fffc13b 0xe7fffe0003fffc13

def z1220 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xffc00ff83ff83e09 0x8ffc00ff83ff83e0

def z1221 : W := mkw 0x00012208061c6206 0x000012208061c620 0xb04fee3cc63ce73f 0xab04fee3cc63ce73

def z1222 : W := mkw 0x8ffeddb7c0000110 0x48ffeddb7c000011 0x8fffffffc0000137 0xf8fffffffc000013

def z1223 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xb04fee3cc63cc733 0x8b04fee3cc63cc73

def z1224 : W := mkw 0x89d6c5b540000000 0x089d6c5b54000000 0x81c7e7fc00000007 0x281c7e7fc0000000

def z1225 : W := mkw 0x8dfec5b540000000 0x08dfec5b54000000 0x8ff7e7f800000001 0x48ff7e7f80000000

def z1226 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0x304fe83cc63ce73a 0x8304fe83cc63ce73

def z1227 : W := mkw 0xaffeddb7d80294a9 0x0affeddb7d80294a 0xcffffffff807d9f7 0xfcffffffff807d9f

def z1228 : W := mkw 0x12025f7c4a483f1e 0x412025f7c4a483f1 0x80001ff800003e04 0x180001ff800003e0

def z1229 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xb04ffe3fc63cffff 0xbb04ffe3fc63cfff

def z1230 : W := mkw 0x8bd6ddb548001408 0x08bd6ddb54800140 0xefc7fff838003e0d 0xfefc7fff838003e0

def z1231 : W := mkw 0x0000024802482a06 0x00000024802482a0 0xf1f81fffc7ffffff 0xff1f81fffc7fffff

def z1232 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xffc01ffc3ffc3f0f 0xfffc01ffc3ffc3f0

def z1233 : W := mkw 0x009726c506d56944 0x8009726c506d5694 0xf1b717c707fff9cf 0x7f1b717c707fff9c

def z1234 : W := mkw 0x009606c502c12944 0x8009606c502c1294 0xd1b017c707c339cd 0x7d1b017c707c339c

def z1235 : W := mkw 0x89d6c5b7c0000000 0x089d6c5b7c000000 0x81c7e7ffc0000001 0x081c7e7ffc000000

def z1236 : W := mkw 0x009766dd46dd6b56 0xc009766dd46dd6b5 0xd1fff7ffc7fff9ff 0x7d1fff7ffc7fff9f

def z1237 : W := mkw 0x009726cd06dd6b56 0xc009726cd06dd6b5 0xf1f71fff07ffffff 0xff1f71fff07fffff

def z1238 : W := mkw 0x1b401b682b683e0e 0x01b401b682b683e0 0xffc01fff3ff83fcd 0xfffc01fff3ff83fc

def z1239 : W := mkw 0x49d5a00025b54000 0x049d5a00025b5400 0x7fcfe0003ffcc00b 0xe7fcfe0003ffcc00

def z1240 : W := mkw 0x009746d546c52944 0x8009746d546c5294 0xd1bff7c7c7c739cf 0x7d1bff7c7c7c739c

def z1241 : W := mkw 0x009604c500c10940 0x8009604c500c1094 0x41b011c701c319c0 0x541b011c701c319c

def z1242 : W := mkw 0x3b401b6aab683eaf 0x03b401b6aab683ea 0xfff01fffffff3fff 0xffff01fffffff3ff

def z1243 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x3fffe0003fffc003 0x83fffe0003fffc00

def z1244 : W := mkw 0x0001024006c52944 0x80001024006c5294 0xd1b017c707c739cf 0x7d1b017c707c739c

def z1245 : W := mkw 0x009402c102c12844 0x8009402c102c1284 0xd1b017c707c739cf 0x7d1b017c707c739c

def z1246 : W := mkw 0x009706c506c52944 0x8009706c506c5294 0xd1b717c707c318c7 0x7d1b717c707c318c

def z1247 : W := mkw 0x0003661c461c6316 0x40003661c461c631 0xb07ffe3fc63ce73f 0xfb07ffe3fc63ce73

def z1248 : W := mkw 0x32025f7eca483fbf 0x432025f7eca483fb 0x80001fffc0003ff4 0x180001fffc0003ff

def z1249 : W := mkw 0x009502c106c52944 0x8009502c106c5294 0xd1b017c307c739cd 0x7d1b017c307c739c

def z1250 : W := mkw 0x26281802980294a9 0x026281802980294a 0xefb81fc7f807ffff 0xfefb81fc7f807fff

def z1251 : W := mkw 0x4dfda00035b7c000 0x04dfda00035b7c00 0x7ffff0073fffc00f 0xf7ffff0073fffc00

def z1252 : W := mkw 0x000366dd465c6b56 0xc000366dd465c6b5 0xf1cfffffc7fcffff 0xff1cfffffc7fcfff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z7,z6]),(0,[z0,z1,z8,z9,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z10,z6]),(0,[z0,z1,z2,z11,z4,z5,z12])],[(0,[z13,z0,z14,z2,z4,z5,z6]),(0,[z0,z1,z2,z15,z4,z5,z6]),(0,[z16,z0,z1,z9,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z17,z18]),(0,[z0,z1,z19,z2,z4,z5,z20]),(0,[z0,z1,z21,z2,z4,z5,z22]),(0,[z0,z1,z2,z4,z5,z20,z20])],[(0,[z0,z1,z2,z4,z5,z23,z6]),(0,[z24,z0,z25,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z26,z6]),(0,[z27,z0,z1,z2,z4,z5,z6])],[(0,[z28,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z29,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z30,z5,z6]),(0,[z0,z1,z31,z2,z4,z5,z6]),(0,[z0,z1,z4,z32,z5,z33,z6]),(0,[z0,z1,z2,z4,z5,z34,z33]),(0,[z0,z1,z2,z4,z35,z5,z6]),(0,[z0,z1,z36,z2,z4,z5,z6])],[(0,[z0,z14,z2,z4,z5,z6,z37]),(0,[z0,z1,z2,z4,z5,z38,z6]),(0,[z39,z0,z1,z2,z40,z5,z6]),(0,[z1,z2,z40,z4,z41,z5,z6]),(0,[z13,z0,z1,z2,z4,z42,z6]),(0,[z0,z1,z2,z4,z5,z6,z43]),(0,[z0,z1,z2,z4,z5,z44,z6])],[(0,[z0,z1,z2,z4,z5,z6,z45]),(0,[z0,z1,z46,z2,z4,z5,z6]),(0,[z0,z47,z1,z2,z4,z5,z6]),(0,[z0,z1,z48,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z18]),(0,[z0,z1,z2,z4,z49,z5,z6])],[(0,[z0,z1,z2,z4,z50,z5,z6]),(0,[z0,z1,z2,z51,z4,z5,z6]),(0,[z13,z0,z1,z52,z4,z5,z6]),(0,[z0,z1,z53,z2,z4,z5,z6]),(0,[z0,z1,z54,z2,z4,z5,z20]),(0,[z55,z0,z1,z2,z4,z5,z18])],[(0,[z56,z0,z1,z2,z4,z5,z6]),(0,[z57,z0,z14,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z0,z1,z2,z4,z58,z5,z6])]],
   [[(0,[z24,z0,z59,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z60,z5,z6]),(0,[z0,z1,z2,z61,z4,z5,z6]),(0,[z0,z1,z2,z62,z4,z5,z6]),(0,[z63,z64,z1,z2,z4,z5,z6]),(0,[z0,z1,z19,z4,z5,z6,z65])],[(1,[z0,z14,z2,z4,z5,z6]),(1,[z59,z2,z4,z41,z5,z6]),(0,[z0,z1,z2,z66,z4,z5,z67]),(0,[z0,z1,z31,z2,z4,z5,z20]),(1,[z0,z1,z68,z2,z4,z5]),(0,[z0,z1,z69,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z35,z5,z20])],[(0,[z0,z1,z70,z2,z4,z5,z6]),(0,[z71,z0,z72,z2,z4,z5,z6]),(0,[z73,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z74,z6]),(0,[z0,z1,z19,z2,z4,z5,z65]),(0,[z0,z1,z2,z75,z4,z5,z6])],[(0,[z76,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z77]),(0,[z0,z1,z78,z2,z4,z5,z6])],[(0,[z0,z14,z2,z4,z79,z5,z6]),(0,[z0,z14,z2,z4,z80,z5,z6]),(1,[z0,z1,z2,z4,z42,z6]),(1,[z0,z1,z2,z4,z5,z81]),(0,[z0,z1,z2,z4,z5,z6,z82])],[(0,[z16,z0,z1,z19,z2,z4,z5]),(0,[z0,z83,z1,z2,z4,z5,z6]),(0,[z13,z0,z84,z2,z4,z5,z6]),(0,[z0,z1,z85,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z86,z65])],[(1,[z0,z1,z52,z4,z5,z6]),(0,[z0,z87,z1,z2,z4,z5,z18]),(1,[z0,z1,z4,z5,z6,z88])],[(0,[z89,z0,z14,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z41,z5,z6]),(1,[z0,z14,z2,z4,z5,z20]),(0,[z0,z14,z2,z4,z90,z5,z6]),(0,[z0,z1,z91,z2,z4,z5,z6]),(0,[z92,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z93,z2,z4,z5,z6]),(0,[z0,z1,z94,z2,z4,z6,z65]),(0,[z0,z1,z95,z4,z5,z6,z96]),(0,[z0,z1,z2,z4,z5,z97,z6])]],
   [[(0,[z98,z0,z1,z2,z4,z5,z18]),(0,[z0,z99,z1,z2,z4,z100,z6]),(0,[z101,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z102,z6]),(0,[z0,z1,z2,z103,z4,z5,z6])],[],[(0,[z0,z14,z2,z4,z5,z104,z6]),(0,[z105,z0,z106,z2,z4,z5,z6])],[(0,[z0,z14,z2,z4,z5,z6,z17]),(0,[z57,z0,z107,z2,z4,z5,z6]),(0,[z108,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z109,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z110,z5,z6]),(0,[z0,z1,z111,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z112,z6]),(0,[z0,z1,z2,z4,z113,z5,z6])],[(0,[z114,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z79,z5,z115]),(0,[z0,z1,z2,z4,z32,z5,z20]),(0,[z116,z0,z1,z2,z4,z5,z6])],[(0,[z0,z59,z2,z40,z4,z5,z6]),(0,[z0,z59,z2,z117,z4,z5,z6]),(1,[z0,z107,z2,z4,z5,z6]),(0,[z118,z0,z1,z2,z4,z5,z6]),(0,[z13,z0,z1,z2,z4,z30,z6]),(0,[z0,z1,z119,z2,z66,z5,z6]),(0,[z120,z0,z1,z2,z4,z5,z6])],[(0,[z89,z0,z59,z2,z4,z5,z6])],[(0,[z98,z16,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z121,z4,z5,z6])]],
   [[(0,[z0,z59,z2,z122,z4,z5,z6]),(1,[z0,z123,z2,z4,z5,z6]),(0,[z0,z1,z31,z2,z4,z34,z6])],[(0,[z124,z0,z14,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z110,z5,z20]),(0,[z0,z1,z125,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z112,z20])],[(0,[z0,z59,z59,z2,z4,z5,z6]),(0,[z0,z59,z2,z4,z5,z126,z6]),(0,[z63,z0,z14,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z127]),(0,[z0,z1,z2,z122,z4,z5,z18]),(0,[z0,z1,z54,z2,z110,z5,z6]),(0,[z0,z1,z48,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z5,z128,z6]),(0,[z0,z1,z2,z4,z5,z33,z96]),(0,[z0,z1,z129,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z130]),(0,[z0,z1,z2,z11,z4,z5,z6])],[(0,[z0,z14,z1,z2,z4,z5,z6]),(0,[z0,z1,z59,z2,z4,z5,z18]),(1,[z0,z106,z2,z4,z5,z6]),(0,[z131,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z35,z79,z6]),(0,[z0,z1,z2,z4,z5,z132,z6]),(0,[z0,z1,z2,z4,z5,z34,z6])],[(0,[z1,z59,z2,z4,z5,z133,z6]),(0,[z39,z0,z134,z2,z4,z5,z6]),(0,[z71,z0,z1,z2,z4,z135,z6]),(1,[z0,z1,z2,z4,z30,z6]),(0,[z0,z1,z2,z4,z5,z136,z18]),(0,[z0,z1,z137,z2,z4,z5,z6]),(0,[z138,z0,z1,z2,z4,z5,z18])],[],[(0,[z76,z0,z59,z2,z4,z5,z6]),(0,[z0,z1,z139,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z140]),(0,[z57,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z141,z4,z5,z6]),(0,[z0,z142,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z143,z110,z5,z6]),(0,[z0,z1,z2,z35,z5,z126,z6])],[(0,[z144,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z119,z145,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z115]),(0,[z146,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z147,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z22]),(0,[z0,z1,z2,z4,z148,z5,z6])],[(0,[z0,z59,z2,z4,z100,z5,z6]),(0,[z0,z149,z1,z2,z4,z5,z6]),(0,[z0,z14,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z5,z150,z6]),(1,[z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z34,z20])],[(0,[z57,z1,z2,z4,z79,z5,z6]),(0,[z0,z1,z2,z4,z151,z5,z6]),(0,[z0,z1,z2,z4,z5,z152,z6]),(0,[z0,z1,z21,z2,z4,z5,z44])],[(0,[z0,z1,z2,z4,z5,z153,z6]),(0,[z0,z1,z2,z4,z100,z5,z18]),(0,[z154,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z155,z6]),(0,[z156,z0,z1,z2,z4,z5,z6])],[(0,[z157,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z158,z4,z5,z6]),(0,[z0,z1,z19,z2,z4,z5,z33]),(0,[z0,z1,z2,z11,z35,z5,z6])],[(0,[z0,z1,z2,z4,z5,z159,z6]),(0,[z0,z1,z2,z160,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z161,z6]),(0,[z0,z1,z2,z162,z4,z5,z6]),(0,[z163,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z164,z2,z4,z5,z6]),(0,[z0,z1,z165,z2,z4,z5,z6])],[(0,[z166,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z167,z6]),(0,[z0,z1,z2,z4,z5,z168,z6]),(0,[z0,z1,z2,z169,z4,z5,z6]),(0,[z0,z1,z9,z2,z4,z5,z18])]],
   [[(0,[z0,z1,z19,z4,z32,z5,z6])],[(0,[z0,z1,z170,z2,z4,z5,z6]),(0,[z13,z171,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z172,z4,z5,z6]),(0,[z0,z1,z2,z4,z173,z5,z6]),(0,[z0,z1,z174,z2,z4,z5,z6])],[(0,[z175,z0,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z176,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z177]),(0,[z0,z1,z2,z4,z5,z178,z6])],[(0,[z89,z1,z2,z4,z79,z5,z6]),(0,[z0,z1,z2,z179,z4,z5,z6]),(0,[z98,z0,z142,z2,z4,z5,z6]),(0,[z0,z99,z1,z2,z4,z5,z18]),(0,[z180,z0,z1,z2,z4,z5,z6])],[(0,[z71,z1,z2,z4,z5,z135,z6]),(0,[z0,z1,z181,z2,z4,z5,z6]),(0,[z0,z1,z182,z2,z4,z5,z6]),(0,[z0,z1,z183,z2,z4,z5,z6]),(0,[z184,z0,z1,z2,z4,z5,z6]),(0,[z0,z185,z1,z2,z4,z5,z6])],[(0,[z166,z0,z1,z2,z4,z5,z20]),(0,[z0,z1,z84,z4,z110,z5,z6]),(0,[z0,z1,z2,z4,z5,z186,z6]),(1,[z0,z1,z2,z4,z5,z187])],[(1,[z59,z2,z145,z4,z5,z6]),(0,[z89,z1,z2,z4,z41,z5,z6]),(0,[z0,z14,z2,z122,z4,z5,z6]),(0,[z0,z1,z2,z188,z4,z5,z6]),(0,[z0,z1,z2,z189,z4,z5,z6]),(0,[z0,z1,z190,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z33,z6,z65])],[(0,[z1,z191,z2,z145,z4,z5,z6]),(0,[z0,z1,z192,z2,z4,z5,z6]),(0,[z193,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z194,z5,z6]),(0,[z0,z1,z195,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z196,z6]),(0,[z0,z1,z197,z2,z4,z5,z6])]],
   [[(0,[z0,z14,z59,z2,z4,z5,z6]),(0,[z55,z0,z14,z2,z4,z5,z6]),(0,[z0,z1,z2,z198,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z199]),(0,[z0,z1,z31,z48,z4,z5,z6])],[(0,[z0,z14,z2,z4,z5,z136,z6]),(0,[z0,z1,z2,z4,z5,z6,z200]),(0,[z0,z201,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z6,z65])],[(0,[z0,z1,z202,z2,z4,z5,z6]),(1,[z203,z1,z2,z4,z5,z6]),(0,[z171,z0,z2,z61,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z81])],[(0,[z204,z0,z14,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z205,z5,z6]),(1,[z206,z0,z2,z4,z5,z6]),(0,[z0,z1,z207,z2,z4,z5,z6]),(0,[z0,z1,z31,z2,z4,z32,z6])],[(0,[z71,z0,z1,z31,z2,z4,z6]),(0,[z0,z1,z208,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z209,z6]),(0,[z0,z1,z210,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z211])],[(0,[z0,z1,z212,z2,z145,z4,z6]),(0,[z0,z1,z2,z4,z213,z5,z6]),(0,[z0,z1,z214,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z215,z5,z6]),(0,[z0,z2,z4,z5,z216,z6,z37]),(0,[z0,z1,z2,z4,z5,z217,z6]),(0,[z0,z1,z48,z2,z4,z32,z6]),(0,[z0,z1,z2,z4,z5,z218,z18])],[(0,[z0,z219,z14,z2,z4,z5,z6]),(0,[z0,z14,z220,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z221,z6]),(0,[z0,z1,z2,z4,z5,z222,z6]),(0,[z0,z1,z2,z66,z4,z5,z6]),(0,[z0,z1,z2,z117,z5,z20,z6]),(0,[z0,z1,z95,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z90,z5,z96])],[(0,[z24,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z61,z4,z110,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z223]),(0,[z0,z1,z31,z2,z4,z5,z224]),(0,[z0,z1,z48,z2,z4,z126,z6]),(0,[z0,z1,z2,z4,z5,z6,z225])]],
   [[(0,[z0,z1,z2,z4,z5,z20,z17]),(0,[z0,z1,z226,z2,z4,z5,z6]),(0,[z0,z1,z227,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z67])],[(0,[z0,z1,z2,z4,z5,z6,z228])],[(0,[z1,z59,z2,z4,z79,z5,z6]),(0,[z229,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z230,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z231]),(0,[z13,z0,z1,z2,z4,z5,z232]),(0,[z0,z1,z2,z233,z4,z5,z6]),(0,[z0,z1,z2,z117,z4,z5,z20])],[(0,[z0,z59,z2,z4,z5,z234,z6]),(0,[z0,z14,z9,z2,z4,z5,z6]),(0,[z105,z0,z1,z2,z4,z5,z20]),(0,[z71,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z133,z6]),(0,[z235,z0,z1,z2,z4,z5,z6]),(0,[z236,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z237,z2,z4,z5,z18])],[(0,[z0,z59,z2,z4,z41,z5,z6]),(0,[z0,z59,z2,z4,z90,z5,z6]),(0,[z0,z0,z14,z2,z4,z5,z6]),(0,[z0,z1,z191,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z238,z6]),(0,[z0,z1,z68,z2,z4,z5,z239]),(0,[z0,z1,z2,z240,z4,z5,z6])],[(0,[z241,z0,z1,z2,z4,z5,z6]),(1,[z0,z142,z2,z4,z5,z6]),(0,[z13,z0,z1,z2,z4,z5,z20]),(0,[z242,z0,z99,z2,z4,z5,z6]),(0,[z0,z1,z54,z119,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z243,z6]),(0,[z0,z1,z244,z2,z4,z5,z6])],[(1,[z0,z245,z2,z4,z5,z6]),(0,[z0,z246,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z41,z5,z18]),(0,[z0,z1,z107,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z115]),(0,[z0,z1,z84,z2,z4,z5,z6]),(0,[z0,z2,z4,z100,z5,z136,z6]),(0,[z247,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z19,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z22])],[(0,[z105,z1,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z248,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z249]),(1,[z0,z1,z54,z110,z5,z6]),(0,[z0,z1,z2,z4,z5,z33,z6]),(0,[z0,z1,z2,z4,z5,z126,z20]),(0,[z0,z1,z2,z4,z5,z250,z18])]],
   [[(0,[z0,z59,z2,z4,z5,z6,z17]),(0,[z251,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z252,z5,z6]),(0,[z63,z98,z0,z1,z2,z4,z5]),(0,[z253,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z254,z4,z5,z6]),(0,[z0,z1,z255,z2,z4,z5,z6]),(1,[z0,z1,z94,z2,z4,z6]),(0,[z0,z1,z4,z5,z6,z88,z96]),(0,[z0,z1,z2,z4,z5,z6,z96])],[(0,[z98,z0,z59,z2,z4,z5,z6]),(0,[z0,z59,z2,z4,z5,z239,z6]),(0,[z0,z14,z256,z2,z4,z5,z6]),(0,[z0,z1,z123,z2,z4,z5,z6]),(1,[z0,z1,z257,z2,z4,z6]),(0,[z0,z1,z2,z258,z4,z5,z6]),(0,[z0,z1,z2,z4,z259,z5,z6]),(0,[z0,z1,z21,z2,z11,z5,z6])],[(0,[z0,z72,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z35,z135,z6]),(1,[z57,z1,z2,z4,z79,z6]),(0,[z0,z1,z2,z260,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z232]),(0,[z0,z1,z2,z4,z261,z5,z6])],[(0,[z0,z262,z1,z2,z4,z5,z6]),(0,[z0,z1,z54,z2,z4,z5,z6]),(0,[z0,z1,z66,z4,z110,z5,z6]),(0,[z0,z1,z2,z4,z5,z263,z6]),(0,[z0,z1,z2,z4,z5,z239,z18])],[(0,[z264,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z84,z2,z4,z5,z20]),(0,[z0,z99,z1,z2,z4,z136,z6]),(0,[z0,z265,z1,z2,z4,z5,z6]),(0,[z0,z1,z9,z2,z4,z90,z5]),(0,[z0,z1,z2,z4,z5,z18,z266])],[(0,[z89,z0,z1,z2,z4,z5,z6]),(0,[z24,z1,z2,z145,z4,z5,z6]),(0,[z0,z1,z106,z2,z4,z5,z6]),(0,[z242,z0,z1,z2,z4,z100,z6]),(0,[z0,z1,z2,z267,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z33,z20]),(0,[z0,z1,z21,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z34,z6,z96])],[(0,[z0,z59,z268,z2,z4,z5,z6]),(1,[z0,z262,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z135,z6]),(0,[z0,z2,z122,z4,z269,z5,z6]),(0,[z251,z0,z1,z2,z4,z5,z20]),(1,[z0,z1,z2,z4,z90,z34])],[(0,[z0,z14,z201,z2,z4,z5,z6]),(0,[z39,z0,z1,z2,z4,z5,z270]),(0,[z0,z1,z2,z271,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z272])]],
   [[(0,[z0,z59,z8,z2,z4,z5,z6]),(0,[z0,z1,z273,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z274,z6]),(0,[z0,z1,z275,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z276,z5,z6])],[(0,[z105,z0,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z277]),(0,[z278,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z279,z5,z6]),(0,[z0,z1,z2,z280,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z281]),(0,[z0,z1,z282,z2,z4,z5,z20])],[(0,[z283,z0,z1,z2,z4,z5,z6]),(0,[z63,z0,z1,z2,z4,z5,z216]),(0,[z0,z1,z284,z2,z4,z5,z6]),(0,[z285,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z8,z2,z4,z5,z18])],[(0,[z13,z0,z59,z2,z4,z5,z6]),(0,[z89,z0,z1,z2,z4,z5,z20]),(0,[z0,z286,z1,z2,z4,z5,z6]),(0,[z16,z0,z1,z2,z4,z5,z18]),(0,[z98,z0,z1,z2,z4,z5,z96]),(0,[z13,z287,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z288,z6]),(0,[z0,z1,z2,z4,z5,z65,z18]),(0,[z0,z1,z2,z289,z4,z5,z6]),(0,[z0,z1,z21,z2,z4,z5,z20])],[(0,[z0,z290,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z135,z20])],[(0,[z0,z1,z2,z4,z291,z5,z6]),(0,[z39,z105,z1,z2,z4,z5,z6]),(0,[z39,z0,z1,z292,z4,z5,z6]),(0,[z0,z1,z2,z293,z4,z5,z6]),(0,[z0,z294,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z86]),(0,[z0,z1,z2,z11,z4,z126,z6])],[(0,[z0,z1,z2,z4,z5,z6,z295]),(0,[z98,z0,z1,z2,z4,z5,z133])],[(0,[z0,z14,z237,z2,z4,z5,z6]),(0,[z124,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z296]),(1,[z0,z1,z2,z4,z297,z6]),(0,[z13,z0,z1,z2,z269,z5,z6]),(0,[z0,z1,z2,z4,z298,z5,z6]),(0,[z0,z1,z2,z4,z5,z299,z6])]],
   [[(0,[z300,z0,z1,z2,z4,z5,z6]),(0,[z14,z1,z59,z2,z4,z5,z6]),(0,[z0,z59,z2,z4,z5,z216,z6]),(0,[z0,z14,z191,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z37]),(0,[z0,z1,z54,z2,z66,z5,z6]),(0,[z0,z1,z301,z2,z4,z5,z6])],[(0,[z57,z0,z59,z2,z4,z5,z6]),(0,[z166,z1,z191,z2,z4,z5,z6]),(0,[z0,z1,z2,z302,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z303,z6]),(0,[z0,z1,z2,z4,z5,z304,z6]),(0,[z206,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z305,z6]),(0,[z0,z1,z2,z4,z32,z5,z6])],[(0,[z0,z1,z2,z4,z5,z216,z18]),(0,[z306,z0,z1,z2,z4,z5,z6])],[(1,[z0,z59,z2,z4,z5,z6]),(0,[z105,z0,z1,z2,z40,z5,z6]),(1,[z193,z1,z2,z4,z5,z6]),(1,[z287,z1,z2,z4,z5,z6]),(0,[z13,z307,z1,z2,z4,z5,z6]),(0,[z0,z256,z1,z2,z4,z5,z18]),(0,[z0,z308,z1,z2,z4,z5,z6])],[(0,[z0,z1,z309,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z135,z126,z6]),(0,[z0,z1,z2,z4,z310,z5,z18]),(0,[z311,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z312,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z67])],[(0,[z0,z1,z313,z2,z4,z5,z6]),(0,[z314,z0,z1,z2,z4,z5,z6]),(0,[z63,z0,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z5,z20,z6,z18]),(0,[z0,z1,z2,z4,z5,z6,z315])],[(0,[z0,z316,z14,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z5,z239,z6]),(0,[z0,z1,z317,z2,z4,z5,z6]),(0,[z98,z0,z318,z2,z4,z5,z6]),(0,[z0,z1,z319,z2,z4,z5,z6]),(0,[z307,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z305,z20])]],
   [[(0,[z0,z1,z2,z4,z5,z320,z6]),(0,[z24,z166,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z79,z5,z6]),(0,[z0,z1,z54,z2,z4,z5,z321]),(0,[z0,z1,z31,z2,z4,z35,z6]),(0,[z0,z1,z2,z322,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z323,z6])],[(1,[z0,z59,z2,z4,z5,z20]),(0,[z175,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z324,z6]),(0,[z0,z1,z2,z4,z5,z6,z325]),(0,[z0,z1,z2,z4,z326,z5,z6]),(0,[z0,z1,z327,z2,z4,z5,z6])],[(1,[z0,z1,z202,z2,z4,z5]),(1,[z0,z1,z2,z4,z328,z6]),(0,[z16,z0,z201,z1,z2,z4,z5]),(0,[z329,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z330,z6]),(0,[z0,z1,z48,z2,z4,z35,z6])],[(0,[z0,z1,z331,z2,z4,z5,z6]),(1,[z307,z1,z2,z4,z5,z6]),(0,[z332,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z333,z5,z6]),(0,[z0,z1,z2,z334,z4,z5,z6])],[(0,[z0,z99,z59,z2,z4,z5,z6]),(0,[z171,z0,z14,z2,z4,z5,z6]),(0,[z335,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z336,z4,z5,z6]),(0,[z0,z1,z2,z4,z337,z5,z6]),(0,[z13,z0,z256,z2,z4,z5,z6]),(1,[z338,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z12,z6])],[(0,[z0,z1,z2,z4,z339,z5,z6])],[(0,[z0,z59,z2,z4,z5,z136,z6]),(0,[z0,z1,z2,z4,z5,z6,z340]),(0,[z0,z14,z8,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z104,z6]),(0,[z0,z1,z2,z4,z79,z5,z20])],[(0,[z0,z1,z2,z4,z5,z6,z341]),(0,[z0,z342,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z343,z2,z4,z5,z6]),(0,[z242,z0,z1,z2,z4,z5,z18]),(1,[z0,z1,z2,z4,z5,z44]),(0,[z0,z1,z2,z4,z344,z5,z6]),(0,[z0,z1,z2,z345,z4,z5,z6])],[(0,[z0,z59,z2,z145,z4,z5,z6]),(0,[z0,z1,z2,z346,z4,z5,z6]),(0,[z0,z1,z2,z4,z90,z5,z20]),(0,[z0,z1,z8,z2,z4,z90,z6])],[(0,[z166,z0,z347,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z133,z6,z17]),(1,[z13,z0,z2,z269,z5,z6]),(0,[z0,z1,z2,z348,z4,z5,z6]),(0,[z0,z1,z48,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z6,z218])],[(0,[z0,z59,z119,z2,z4,z5,z6]),(0,[z0,z1,z2,z145,z4,z5,z18]),(0,[z349,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z350,z4,z5,z6])],[(0,[z63,z0,z59,z2,z4,z5,z6])],[(0,[z71,z0,z14,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z6]),(0,[z0,z203,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z61,z4,z5,z18]),(0,[z0,z1,z2,z4,z351,z5,z6]),(0,[z0,z1,z119,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z352,z6]),(0,[z0,z1,z19,z9,z4,z5,z6])],[(0,[z353,z0,z1,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z5,z216,z6]),(1,[z16,z1,z2,z4,z5,z17]),(0,[z0,z1,z119,z61,z4,z5,z6]),(0,[z64,z0,z1,z2,z4,z5,z6]),(1,[z63,z0,z2,z4,z5,z216]),(1,[z0,z1,z2,z4,z5,z281]),(0,[z0,z1,z2,z4,z5,z6,z354])],[(0,[z0,z1,z2,z4,z355,z5,z6]),(0,[z0,z1,z2,z2,z4,z5,z6]),(1,[z0,z1,z356,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z177,z6]),(0,[z0,z1,z4,z32,z5,z239,z6]),(0,[z0,z357,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z59,z9,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z358,z5,z6]),(0,[z0,z1,z2,z4,z5,z359,z6]),(0,[z0,z1,z2,z4,z5,z6,z360])],[(0,[z0,z59,z2,z361,z4,z5,z6]),(0,[z0,z1,z2,z362,z4,z5,z6]),(1,[z0,z318,z2,z4,z5,z6]),(0,[z0,z1,z2,z363,z4,z5,z6])],[(0,[z0,z1,z364,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z365,z5,z6]),(0,[z0,z1,z366,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z367]),(0,[z0,z1,z119,z84,z4,z5,z6]),(0,[z0,z1,z2,z4,z368,z5,z6])],[(0,[z0,z59,z2,z4,z269,z5,z6]),(0,[z369,z0,z1,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z5,z20,z6]),(0,[z0,z1,z2,z4,z5,z370,z6]),(0,[z0,z1,z2,z371,z4,z5,z6]),(1,[z0,z372,z2,z4,z5,z6]),(0,[z0,z220,z1,z2,z4,z5,z18]),(0,[z55,z0,z1,z2,z4,z5,z20])],[(0,[z0,z364,z59,z2,z4,z5,z6]),(0,[z39,z0,z14,z2,z4,z5,z6]),(0,[z0,z220,z1,z61,z4,z5,z6]),(0,[z0,z1,z2,z373,z4,z5,z6]),(0,[z0,z1,z374,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z269,z5,z18])],[(0,[z76,z0,z1,z59,z2,z4,z5]),(0,[z0,z1,z2,z4,z375,z5,z6]),(0,[z0,z1,z2,z376,z4,z5,z6]),(1,[z166,z1,z191,z4,z5,z6]),(0,[z0,z1,z2,z4,z377,z5,z6]),(0,[z0,z1,z378,z2,z4,z5,z6]),(0,[z0,z1,z379,z2,z4,z5,z6])]],
   [[(0,[z98,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z380,z4,z5,z6]),(0,[z0,z1,z2,z4,z381,z5,z6]),(0,[z0,z1,z2,z11,z4,z35,z6]),(0,[z0,z1,z2,z4,z90,z34,z6])],[(0,[z0,z1,z382,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z383,z5,z6]),(0,[z0,z1,z384,z2,z4,z5,z6]),(0,[z0,z1,z2,z66,z4,z385,z6])],[(0,[z0,z220,z1,z84,z4,z5,z6]),(0,[z0,z386,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z66,z4,z263,z6])],[(0,[z0,z1,z2,z4,z387,z5,z6]),(0,[z0,z14,z2,z4,z5,z23,z6]),(0,[z0,z1,z388,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z389,z5,z6]),(0,[z0,z1,z2,z4,z390,z5,z6]),(0,[z0,z1,z391,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z392,z6]),(0,[z0,z1,z2,z4,z5,z393,z6])],[(0,[z0,z14,z31,z2,z4,z5,z6]),(0,[z394,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z395,z6]),(0,[z0,z396,z1,z2,z4,z5,z6])],[(0,[z0,z1,z397,z2,z4,z5,z6]),(0,[z0,z398,z59,z2,z4,z5,z6]),(0,[z16,z0,z14,z2,z4,z5,z6]),(0,[z171,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z187,z6]),(0,[z0,z1,z2,z4,z5,z20,z399])],[(0,[z400,z0,z1,z2,z4,z5,z18]),(0,[z0,z59,z2,z4,z5,z401,z6]),(0,[z0,z14,z48,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z5,z6,z18]),(0,[z0,z1,z2,z4,z5,z402,z6]),(0,[z98,z0,z1,z2,z4,z5,z20]),(0,[z171,z0,z1,z61,z4,z5,z6]),(0,[z0,z1,z2,z4,z403,z5,z6]),(0,[z0,z1,z404,z2,z4,z5,z6])],[(0,[z0,z14,z2,z145,z4,z5,z6]),(0,[z0,z1,z2,z40,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z199,z6]),(0,[z0,z1,z2,z117,z4,z5,z6])]],
   [[(0,[z405,z0,z1,z2,z4,z5,z6]),(0,[z105,z0,z1,z2,z4,z5,z6]),(0,[z63,z16,z0,z1,z2,z4,z5]),(0,[z0,z1,z31,z2,z4,z126,z6]),(0,[z0,z1,z2,z11,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z18,z18])],[(0,[z0,z14,z119,z2,z4,z5,z6]),(0,[z0,z14,z2,z61,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z406,z6]),(0,[z242,z0,z1,z2,z4,z136,z6]),(0,[z0,z201,z2,z4,z5,z6,z37]),(0,[z0,z1,z407,z2,z4,z5,z6]),(0,[z408,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z31,z19,z4,z5,z6]),(0,[z0,z1,z2,z4,z409,z5,z6]),(0,[z0,z1,z410,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z34,z18])],[(0,[z55,z0,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z411,z5,z6]),(0,[z0,z1,z2,z4,z5,z412,z6]),(0,[z13,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z395,z20])],[(0,[z0,z290,z1,z2,z4,z5,z6]),(1,[z0,z1,z312,z2,z4,z5]),(0,[z413,z0,z1,z2,z4,z5,z6]),(0,[z414,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z415,z2,z4,z5,z6]),(0,[z171,z0,z1,z84,z4,z5,z6]),(0,[z63,z0,z201,z2,z4,z5,z6])],[(0,[z0,z59,z237,z2,z4,z5,z6]),(0,[z0,z1,z59,z2,z4,z5,z6]),(0,[z0,z25,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z341]),(0,[z0,z1,z2,z416,z4,z5,z6]),(1,[z417,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z418,z5,z6]),(0,[z0,z1,z2,z4,z5,z126,z6]),(0,[z0,z419,z1,z2,z4,z5,z20])],[(0,[z0,z59,z191,z2,z4,z5,z6]),(0,[z0,z1,z2,z40,z4,z5,z20]),(0,[z13,z0,z1,z2,z122,z5,z6]),(0,[z420,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z421,z6]),(0,[z0,z1,z422,z2,z4,z5,z6])],[(0,[z63,z0,z1,z2,z4,z5,z37]),(0,[z0,z1,z2,z4,z5,z423,z18])],[(1,[z71,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z424]),(0,[z425,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z1,z59,z2,z4,z41,z5,z6]),(0,[z57,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z426,z2,z4,z5,z6]),(0,[z427,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z428]),(0,[z0,z1,z2,z122,z4,z5,z20]),(0,[z0,z1,z429,z2,z4,z5,z6]),(0,[z0,z1,z4,z110,z32,z5,z6]),(0,[z0,z1,z430,z2,z4,z5,z18])],[],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z59,z2,z4,z5,z20]),(0,[z431,z0,z1,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z269,z5,z6]),(0,[z0,z256,z2,z122,z4,z5,z6]),(0,[z0,z1,z31,z4,z5,z239,z6]),(0,[z0,z1,z432,z2,z4,z5,z6]),(0,[z0,z433,z1,z2,z4,z5,z6])],[(0,[z166,z0,z1,z145,z4,z5,z6]),(0,[z434,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z435]),(0,[z98,z0,z1,z9,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z136,z20])],[(0,[z0,z256,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z436,z6]),(0,[z0,z437,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z438]),(0,[z0,z1,z2,z4,z5,z6,z439]),(0,[z0,z1,z2,z4,z440,z5,z6]),(0,[z0,z1,z2,z4,z100,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z441])],[(0,[z71,z57,z1,z2,z4,z5,z6]),(0,[z0,z442,z1,z2,z4,z5,z6]),(0,[z171,z203,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z443]),(0,[z0,z1,z444,z2,z4,z5,z6]),(0,[z0,z1,z21,z2,z5,z126,z6]),(0,[z0,z1,z2,z4,z5,z445,z6]),(0,[z0,z1,z275,z2,z4,z5,z6]),(0,[z0,z1,z446,z2,z4,z5,z18]),(0,[z0,z1,z8,z2,z4,z5,z96])],[(0,[z0,z0,z59,z2,z4,z5,z6]),(0,[z39,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z447,z6]),(0,[z57,z0,z1,z2,z4,z5,z20]),(0,[z16,z0,z1,z2,z4,z5,z96]),(0,[z0,z1,z2,z4,z5,z37,z18]),(0,[z0,z1,z282,z2,z4,z5,z6]),(1,[z0,z1,z237,z2,z5,z18]),(0,[z0,z1,z174,z2,z4,z5,z18])],[(0,[z448,z0,z1,z2,z4,z5,z6]),(0,[z13,z0,z1,z53,z4,z5,z6])]],
   [[(0,[z449,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z212,z2,z4,z6]),(0,[z0,z1,z202,z2,z145,z4,z5]),(1,[z0,z437,z2,z4,z5,z6]),(0,[z0,z1,z450,z2,z4,z5,z6]),(0,[z0,z256,z1,z2,z269,z5,z6]),(0,[z0,z1,z2,z4,z451,z5,z6]),(0,[z0,z1,z2,z4,z136,z126,z6]),(0,[z0,z1,z2,z4,z35,z100,z6]),(1,[z0,z1,z2,z4,z5,z20]),(0,[z0,z1,z432,z2,z4,z5,z20])],[(0,[z16,z0,z1,z2,z4,z5,z133]),(0,[z0,z452,z1,z2,z4,z5,z6])],[(0,[z0,z59,z2,z4,z453,z5,z6]),(0,[z242,z0,z14,z2,z4,z5,z6]),(0,[z454,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z100,z5,z20])],[(0,[z0,z1,z2,z4,z5,z455,z6]),(0,[z0,z1,z191,z4,z110,z5,z6]),(0,[z39,z0,z1,z2,z41,z5,z6]),(0,[z0,z1,z456,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z457,z5,z6]),(0,[z0,z99,z1,z2,z4,z5,z6]),(0,[z0,z201,z1,z2,z4,z5,z216])],[(0,[z0,z14,z2,z11,z4,z5,z6]),(1,[z98,z1,z2,z4,z5,z133]),(0,[z0,z1,z2,z458,z4,z5,z6])],[(0,[z0,z14,z2,z4,z5,z34,z6]),(0,[z0,z1,z459,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z460,z5,z6])],[(0,[z0,z245,z1,z2,z4,z5,z6])],[(0,[z98,z0,z1,z19,z2,z4,z5]),(1,[z0,z1,z53,z4,z5,z6]),(0,[z0,z1,z2,z461,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z462,z4,z5,z6]),(1,[z0,z25,z2,z4,z5,z6]),(1,[z24,z1,z145,z4,z5,z6]),(0,[z0,z1,z463,z2,z4,z5,z6]),(0,[z0,z1,z464,z2,z4,z5,z6]),(1,[z0,z2,z4,z143,z5,z6]),(0,[z0,z465,z1,z2,z4,z5,z6])],[(0,[z0,z1,z119,z191,z4,z5,z6]),(1,[z0,z466,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z42,z6]),(0,[z0,z467,z1,z2,z4,z5,z6]),(0,[z0,z99,z1,z2,z4,z5,z20]),(0,[z468,z0,z1,z2,z4,z5,z6]),(0,[z469,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z470,z2,z4,z5,z6])],[(0,[z0,z1,z2,z471,z4,z5,z6]),(0,[z0,z1,z318,z2,z4,z5,z6]),(0,[z0,z1,z472,z2,z4,z5,z6])],[(0,[z24,z0,z1,z145,z4,z5,z6]),(0,[z57,z0,z1,z48,z2,z4,z6]),(0,[z63,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z66,z4,z5,z18])],[(0,[z24,z0,z1,z2,z4,z5,z18]),(0,[z338,z242,z1,z2,z4,z5,z6]),(0,[z473,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z119,z66,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z474]),(0,[z0,z1,z2,z4,z5,z475,z6])],[(0,[z1,z2,z4,z79,z5,z135,z6]),(0,[z16,z0,z372,z2,z4,z5,z6]),(0,[z0,z1,z372,z2,z4,z5,z6]),(0,[z0,z476,z1,z2,z4,z5,z6])],[(0,[z89,z1,z2,z145,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z477,z6]),(0,[z0,z1,z9,z2,z4,z5,z65]),(0,[z0,z1,z2,z4,z5,z6,z478])],[(0,[z0,z59,z2,z4,z479,z5,z6]),(0,[z480,z0,z59,z2,z4,z5,z6]),(0,[z0,z14,z2,z160,z4,z5,z6]),(0,[z0,z1,z2,z4,z60,z5,z6]),(0,[z0,z201,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z5,z18,z481])]],
   [[(0,[z16,z1,z2,z4,z5,z6,z17]),(0,[z0,z1,z2,z4,z5,z482,z6]),(1,[z0,z201,z2,z4,z5,z37]),(0,[z483,z0,z1,z2,z4,z5,z6])],[(0,[z0,z59,z2,z4,z5,z20,z6]),(0,[z0,z14,z99,z2,z4,z5,z6]),(0,[z57,z0,z1,z2,z4,z79,z6]),(0,[z0,z1,z2,z4,z484,z5,z6]),(0,[z0,z1,z2,z4,z5,z485,z6]),(0,[z13,z0,z1,z2,z4,z5,z439]),(0,[z242,z0,z2,z4,z100,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z224]),(0,[z0,z1,z2,z4,z4,z5,z18])],[(0,[z0,z1,z2,z4,z486,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z487]),(0,[z63,z0,z2,z4,z5,z216,z6]),(0,[z0,z1,z2,z4,z385,z5,z6]),(0,[z0,z1,z21,z2,z4,z35,z6]),(0,[z0,z1,z2,z4,z5,z20,z488])],[(0,[z0,z1,z2,z4,z80,z5,z6]),(0,[z0,z1,z489,z2,z4,z5,z6]),(0,[z0,z1,z490,z2,z4,z5,z6]),(0,[z0,z1,z491,z2,z4,z5,z6]),(0,[z0,z1,z19,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z20,z18])],[(0,[z492,z0,z1,z2,z4,z5,z6]),(0,[z493,z0,z1,z2,z4,z5,z6])],[(0,[z400,z1,z59,z2,z4,z5,z6]),(0,[z0,z220,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z234,z6]),(0,[z0,z1,z2,z494,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z495,z6]),(0,[z13,z0,z2,z4,z269,z5,z6]),(0,[z0,z1,z2,z4,z5,z496,z6]),(0,[z0,z1,z2,z4,z5,z6,z423])],[(1,[z76,z0,z59,z2,z4,z5]),(0,[z497,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z41,z5,z6]),(0,[z0,z1,z2,z4,z498,z5,z6]),(0,[z499,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z500,z6]),(0,[z0,z1,z2,z4,z5,z501,z6]),(0,[z0,z1,z502,z2,z4,z5,z6]),(0,[z0,z1,z503,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z90,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z504]),(0,[z0,z1,z505,z2,z4,z5,z6])]],
   [[(0,[z400,z0,z14,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z506,z5,z6]),(0,[z0,z99,z2,z4,z5,z136,z6]),(0,[z0,z1,z2,z507,z4,z5,z6]),(0,[z0,z1,z54,z2,z4,z5,z18])],[(0,[z0,z59,z31,z2,z4,z5,z6]),(0,[z0,z59,z2,z4,z35,z5,z6]),(0,[z0,z1,z2,z4,z508,z5,z6]),(0,[z71,z0,z1,z2,z4,z5,z20]),(1,[z0,z1,z2,z4,z5,z439]),(0,[z338,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z48,z2,z4,z239,z6]),(0,[z0,z1,z509,z2,z4,z5,z6]),(0,[z510,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z511,z4,z5,z6]),(0,[z0,z1,z237,z2,z4,z5,z20])],[(0,[z0,z1,z257,z2,z4,z5,z6]),(0,[z0,z1,z191,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z5,z6,z17]),(0,[z0,z220,z84,z2,z4,z5,z6]),(0,[z0,z84,z2,z122,z4,z5,z6]),(0,[z0,z1,z2,z512,z4,z5,z6]),(0,[z0,z1,z94,z2,z4,z5,z6]),(0,[z0,z1,z9,z4,z5,z33,z6]),(0,[z0,z1,z513,z2,z4,z5,z6])],[(0,[z0,z59,z48,z2,z4,z5,z6]),(0,[z0,z59,z2,z4,z5,z6,z18]),(0,[z514,z0,z14,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z135,z18]),(0,[z0,z1,z2,z4,z5,z443,z6]),(0,[z0,z1,z31,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z35,z5,z18])],[(0,[z0,z398,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z41,z5,z20]),(0,[z0,z1,z31,z8,z2,z4,z6])],[(0,[z1,z59,z2,z145,z4,z5,z6]),(0,[z71,z1,z59,z2,z4,z5,z6]),(0,[z0,z201,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z515,z5,z6])],[(1,[z59,z2,z4,z5,z133,z6]),(0,[z171,z0,z59,z2,z4,z5,z6]),(0,[z0,z59,z2,z61,z4,z5,z6]),(0,[z516,z0,z1,z2,z4,z5,z6]),(0,[z171,z193,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z517,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z250])],[(0,[z89,z400,z1,z2,z4,z5,z6]),(0,[z0,z14,z2,z66,z4,z5,z6]),(0,[z0,z1,z2,z4,z518,z5,z6]),(0,[z0,z466,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z519]),(0,[z0,z1,z237,z2,z5,z6,z18])]],
   [[(0,[z0,z1,z268,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z520,z5,z6]),(0,[z0,z1,z2,z4,z521,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z522])],[(0,[z55,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z523]),(0,[z89,z166,z1,z2,z4,z5,z6]),(1,[z0,z14,z2,z4,z5,z18]),(0,[z0,z1,z2,z524,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z525]),(0,[z0,z1,z2,z4,z5,z239,z20])],[(0,[z0,z1,z2,z526,z4,z5,z6]),(1,[z0,z256,z2,z122,z5,z6]),(1,[z0,z1,z2,z4,z5,z12]),(0,[z0,z1,z2,z4,z527,z5,z6])],[(0,[z0,z1,z1,z2,z4,z5,z6]),(0,[z0,z1,z312,z2,z145,z4,z5]),(0,[z0,z1,z2,z4,z5,z528,z6]),(0,[z0,z1,z2,z4,z90,z5,z34])],[(0,[z89,z105,z1,z2,z4,z5,z6]),(0,[z204,z0,z1,z2,z4,z5,z6]),(0,[z171,z0,z220,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z529,z5,z6]),(0,[z0,z1,z48,z4,z32,z5,z6]),(0,[z0,z1,z2,z4,z5,z530,z6])],[(0,[z0,z1,z531,z2,z4,z5,z6]),(0,[z98,z0,z1,z2,z4,z5,z17]),(0,[z532,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z533,z6]),(0,[z0,z1,z2,z4,z5,z6,z534]),(0,[z0,z535,z1,z2,z4,z5,z6])],[(0,[z166,z0,z14,z2,z4,z5,z6]),(1,[z0,z72,z2,z4,z5,z6]),(0,[z71,z0,z1,z48,z2,z4,z6]),(0,[z0,z1,z2,z4,z536,z5,z6]),(0,[z0,z1,z2,z4,z32,z5,z18])],[(0,[z71,z0,z59,z2,z4,z5,z6]),(0,[z0,z14,z19,z2,z4,z5,z6]),(0,[z0,z219,z1,z2,z4,z5,z6]),(0,[z0,z417,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z537,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z538]),(0,[z0,z1,z31,z4,z110,z5,z6]),(0,[z0,z1,z119,z4,z32,z5,z6]),(0,[z0,z1,z539,z2,z4,z5,z6]),(0,[z0,z1,z540,z2,z4,z5,z6])]],
   [[(0,[z166,z0,z1,z191,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z541,z6]),(0,[z0,z1,z2,z4,z5,z542,z6]),(0,[z543,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z8,z2,z4,z5,z20])],[(0,[z0,z59,z2,z4,z110,z5,z6]),(0,[z544,z0,z1,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z5,z6,z96]),(0,[z0,z545,z1,z2,z4,z5,z6]),(0,[z16,z0,z1,z2,z4,z5,z20]),(0,[z0,z1,z546,z2,z4,z5,z6]),(0,[z0,z1,z547,z2,z4,z5,z6]),(0,[z0,z1,z2,z548,z4,z5,z6]),(0,[z0,z1,z9,z2,z4,z5,z33]),(0,[z0,z549,z1,z2,z4,z5,z6]),(0,[z0,z1,z511,z11,z4,z5,z6]),(0,[z0,z87,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z550,z5,z6]),(0,[z0,z1,z2,z4,z5,z216,z6]),(0,[z0,z1,z2,z4,z5,z20,z216])],[(0,[z39,z0,z1,z2,z4,z297,z6]),(0,[z0,z256,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z110,z5,z18]),(0,[z108,z0,z1,z2,z4,z5,z18])],[(0,[z89,z71,z1,z2,z4,z5,z6]),(0,[z0,z14,z54,z2,z4,z5,z6]),(0,[z71,z0,z1,z2,z4,z79,z6]),(0,[z551,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z310,z5,z6]),(0,[z0,z1,z2,z552,z4,z5,z6])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z553,z0,z1,z2,z4,z5,z6]),(1,[z400,z59,z2,z4,z5,z6]),(0,[z16,z1,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z554,z5,z6]),(0,[z0,z1,z2,z4,z555,z5,z6]),(0,[z0,z556,z1,z2,z4,z5,z6])],[(0,[z0,z14,z21,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z557,z5,z6]),(0,[z0,z256,z1,z2,z122,z5,z6]),(0,[z0,z1,z558,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z224])],[(1,[z166,z59,z2,z4,z5,z6]),(0,[z39,z0,z59,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z5,z135,z6]),(0,[z0,z14,z2,z4,z35,z5,z6]),(0,[z0,z1,z2,z4,z559,z5,z6]),(1,[z0,z1,z21,z2,z126,z6])]],
   [[(1,[z0,z398,z59,z2,z4,z5]),(1,[z0,z99,z2,z4,z136,z6]),(0,[z560,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z19,z2,z4,z90,z5]),(0,[z561,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z562,z5,z6])],[(0,[z0,z59,z2,z11,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z563]),(1,[z0,z134,z2,z4,z5,z6]),(0,[z0,z419,z1,z2,z4,z5,z6]),(0,[z0,z256,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z143,z5,z6]),(0,[z0,z1,z237,z2,z117,z5,z6])],[(1,[z14,z59,z2,z4,z5,z6]),(1,[z105,z59,z2,z4,z5,z6]),(0,[z0,z59,z2,z4,z5,z34,z6]),(0,[z16,z0,z466,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z564,z6]),(0,[z242,z417,z1,z2,z4,z5,z6]),(0,[z0,z1,z21,z2,z4,z126,z6]),(0,[z0,z1,z2,z4,z5,z18,z43])],[(0,[z0,z1,z356,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z565,z5,z6]),(0,[z566,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z18,z45]),(0,[z0,z1,z2,z4,z5,z20,z360])],[(0,[z0,z14,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z35,z136,z6]),(0,[z0,z1,z2,z11,z4,z5,z281])],[(0,[z567,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z568,z2,z4,z5,z6]),(1,[z89,z14,z2,z4,z5,z6]),(0,[z569,z0,z1,z2,z4,z5,z6]),(1,[z0,z347,z2,z4,z5,z6]),(0,[z0,z1,z570,z2,z4,z5,z6]),(0,[z0,z1,z2,z122,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z232,z6]),(1,[z0,z1,z2,z4,z385,z6]),(0,[z0,z1,z8,z48,z2,z4,z6])],[(1,[z76,z0,z1,z2,z4,z5]),(0,[z24,z0,z14,z2,z4,z5,z6]),(0,[z39,z0,z1,z2,z4,z328,z6]),(1,[z0,z1,z2,z4,z263,z6]),(0,[z0,z1,z2,z4,z5,z571,z6]),(0,[z0,z1,z2,z4,z562,z5,z20])],[(0,[z16,z0,z59,z2,z4,z5,z6]),(0,[z572,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z573,z2,z4,z5,z6]),(0,[z57,z0,z1,z2,z4,z135,z6]),(0,[z0,z1,z2,z4,z5,z6,z574]),(0,[z0,z201,z1,z2,z4,z5,z37]),(0,[z0,z1,z2,z4,z575,z5,z6])]],
   [[(0,[z0,z14,z2,z4,z5,z6,z296]),(0,[z24,z0,z1,z191,z4,z5,z6]),(1,[z0,z576,z2,z4,z5,z6]),(0,[z98,z0,z1,z2,z4,z5,z34]),(1,[z0,z1,z2,z4,z5,z577]),(0,[z0,z1,z2,z122,z4,z5,z443]),(0,[z242,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z578,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z136,z6]),(0,[z0,z1,z2,z579,z4,z5,z6]),(0,[z138,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z328,z5,z6]),(1,[z0,z1,z4,z517,z5,z6])],[(0,[z580,z0,z1,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z32,z5,z6]),(0,[z581,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z270,z6]),(0,[z0,z582,z1,z2,z4,z5,z6]),(0,[z0,z1,z583,z2,z4,z5,z6])],[(1,[z59,z2,z4,z79,z5,z6]),(0,[z0,z1,z2,z145,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z584,z6]),(0,[z0,z1,z2,z4,z79,z5,z541]),(0,[z0,z1,z2,z585,z4,z5,z6]),(0,[z0,z1,z586,z2,z4,z5,z6])],[(1,[z105,z1,z2,z40,z5,z6]),(0,[z0,z1,z2,z4,z5,z587,z6]),(1,[z0,z1,z19,z4,z5,z65])],[(0,[z0,z398,z1,z59,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z588,z6]),(0,[z0,z1,z119,z2,z4,z5,z6]),(0,[z0,z1,z589,z2,z4,z5,z6])],[(0,[z480,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z590,z2,z4,z5,z6]),(0,[z0,z1,z591,z2,z4,z5,z6]),(0,[z242,z0,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z592,z5,z6])],[(0,[z0,z14,z2,z4,z110,z5,z6]),(0,[z166,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z20,z65]),(0,[z0,z1,z2,z4,z593,z5,z6])]],
   [[(0,[z0,z1,z594,z2,z4,z5,z6]),(0,[z0,z1,z595,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z596,z5,z6]),(0,[z0,z1,z597,z2,z4,z5,z6]),(0,[z0,z1,z48,z2,z4,z5,z20]),(1,[z0,z1,z2,z4,z6,z86])],[(0,[z0,z1,z2,z145,z4,z5,z20]),(0,[z598,z0,z1,z2,z4,z5,z6]),(0,[z0,z287,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z65,z96])],[(0,[z0,z1,z2,z4,z5,z599,z6]),(0,[z0,z1,z9,z2,z4,z5,z6])],[(0,[z0,z1,z2,z361,z4,z5,z6]),(0,[z89,z1,z2,z4,z5,z133,z6]),(0,[z264,z0,z14,z2,z4,z5,z6]),(0,[z39,z0,z1,z356,z4,z5,z6]),(0,[z0,z1,z2,z61,z4,z5,z20]),(0,[z600,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z601,z2,z4,z5,z6]),(0,[z0,z1,z119,z2,z4,z5,z20]),(0,[z602,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z603,z2,z4,z5,z6]),(0,[z0,z220,z1,z2,z4,z5,z6]),(1,[z0,z1,z119,z66,z5,z6])],[(0,[z604,z0,z1,z2,z4,z5,z6]),(0,[z24,z0,z123,z2,z4,z5,z6]),(0,[z605,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z79,z126,z6]),(0,[z0,z1,z54,z2,z4,z5,z81])],[(0,[z0,z568,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z292,z4,z5,z6]),(0,[z0,z1,z2,z4,z269,z5,z6]),(1,[z265,z1,z2,z4,z5,z6]),(0,[z0,z606,z1,z2,z4,z5,z6])],[(0,[z0,z59,z2,z4,z5,z6,z65]),(0,[z0,z1,z2,z607,z4,z5,z6]),(0,[z39,z1,z2,z4,z41,z5,z6]),(0,[z0,z1,z2,z4,z5,z608,z6]),(0,[z0,z1,z2,z609,z4,z5,z6]),(0,[z0,z1,z2,z610,z4,z5,z6])]],
   [[(0,[z0,z316,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z611,z4,z5,z6]),(0,[z0,z1,z2,z612,z4,z5,z6]),(0,[z0,z1,z613,z2,z4,z5,z6]),(0,[z0,z1,z9,z2,z4,z5,z20])],[(0,[z0,z1,z614,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z615,z6]),(0,[z0,z1,z2,z4,z5,z6,z266]),(0,[z0,z1,z2,z4,z5,z6,z616]),(1,[z0,z1,z31,z4,z239,z6])],[(0,[z0,z286,z14,z2,z4,z5,z6]),(1,[z171,z0,z61,z4,z5,z6]),(0,[z0,z220,z1,z2,z4,z5,z20]),(0,[z0,z1,z617,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z618,z6]),(1,[z0,z1,z95,z4,z5,z6])],[(0,[z619,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z9,z4,z5,z33]),(0,[z620,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z11,z35,z6])],[(0,[z0,z59,z2,z66,z4,z5,z6]),(0,[z242,z0,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z297,z6]),(0,[z0,z1,z2,z40,z4,z5,z18]),(0,[z0,z1,z2,z4,z269,z5,z20]),(0,[z0,z201,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z187,z239]),(0,[z0,z1,z11,z4,z517,z5,z6]),(0,[z0,z1,z2,z117,z4,z5,z18])],[(0,[z0,z1,z145,z4,z110,z5,z6]),(0,[z105,z0,z1,z2,z4,z5,z18]),(0,[z171,z0,z1,z2,z4,z5,z6])],[(0,[z400,z0,z1,z2,z4,z5,z6]),(1,[z39,z1,z2,z41,z5,z6]),(0,[z57,z0,z1,z31,z2,z4,z6]),(0,[z621,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z20,z96])],[(0,[z13,z0,z1,z2,z4,z5,z18])]],
   [[(1,[z0,z398,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z401,z6]),(0,[z0,z1,z2,z4,z622,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z623])],[(0,[z0,z59,z2,z4,z5,z133,z6]),(0,[z514,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z40,z4,z5,z500]),(0,[z71,z0,z576,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z20,z133]),(0,[z0,z1,z2,z4,z5,z126,z18])],[(0,[z0,z1,z2,z4,z5,z624,z6]),(0,[z105,z0,z1,z2,z41,z5,z6]),(0,[z0,z625,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z40,z4,z5,z77]),(1,[z0,z1,z2,z4,z5,z321]),(0,[z0,z1,z626,z2,z4,z5,z6]),(0,[z0,z1,z627,z2,z4,z5,z6])],[(0,[z628,z0,z1,z2,z4,z5,z6]),(0,[z57,z0,z442,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z133,z18]),(0,[z171,z0,z1,z2,z4,z5,z20]),(0,[z0,z1,z31,z4,z5,z33,z6]),(0,[z629,z0,z1,z2,z4,z5,z6])],[(0,[z400,z0,z1,z2,z4,z5,z20]),(0,[z0,z59,z19,z2,z4,z5,z6]),(0,[z0,z59,z84,z2,z4,z5,z6]),(0,[z98,z0,z201,z1,z2,z4,z5]),(0,[z0,z1,z630,z2,z4,z5,z6]),(0,[z631,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z632,z5,z6])],[(0,[z0,z59,z2,z4,z5,z33,z6]),(0,[z633,z0,z1,z2,z4,z5,z6]),(1,[z0,z442,z2,z4,z5,z6]),(0,[z0,z634,z1,z2,z4,z5,z6]),(0,[z0,z1,z68,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z488,z6])],[(0,[z0,z59,z2,z4,z5,z6,z96]),(0,[z0,z1,z2,z635,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z636,z6]),(0,[z71,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z84,z2,z4,z5,z18]),(0,[z0,z1,z2,z11,z4,z5,z20]),(0,[z0,z1,z2,z4,z5,z637,z6]),(0,[z0,z1,z237,z2,z4,z5,z6])],[(0,[z0,z1,z191,z2,z4,z5,z6]),(0,[z638,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z639,z2,z4,z5,z6]),(0,[z640,z0,z1,z2,z4,z5,z6]),(0,[z63,z265,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z641,z5,z6]),(0,[z0,z1,z119,z2,z110,z5,z6]),(1,[z0,z1,z48,z4,z32,z6]),(0,[z0,z1,z2,z4,z5,z33,z18]),(0,[z0,z1,z2,z4,z5,z6,z399])]],
   [[(0,[z0,z1,z2,z642,z4,z5,z6]),(0,[z0,z14,z2,z376,z4,z5,z6]),(0,[z643,z0,z1,z2,z4,z5,z6]),(0,[z39,z0,z1,z2,z4,z5,z341]),(0,[z0,z1,z2,z4,z5,z644,z6]),(0,[z0,z1,z430,z2,z4,z5,z6])],[(0,[z0,z59,z54,z2,z4,z5,z6]),(0,[z645,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z481]),(1,[z0,z1,z2,z5,z20,z18]),(0,[z629,z0,z1,z2,z4,z5,z20])],[(0,[z0,z1,z134,z2,z4,z5,z6]),(0,[z0,z1,z646,z2,z4,z5,z6]),(0,[z0,z1,z31,z2,z4,z239,z6])],[(0,[z0,z59,z21,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z647,z6]),(0,[z166,z0,z245,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z270]),(0,[z648,z0,z1,z2,z4,z5,z6]),(0,[z649,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z8,z2,z4,z6,z96])],[(0,[z0,z59,z2,z4,z5,z135,z6]),(0,[z0,z1,z2,z4,z5,z650,z6]),(0,[z0,z14,z388,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z500]),(0,[z0,z1,z651,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z652,z5,z6]),(0,[z0,z1,z2,z66,z4,z5,z199]),(0,[z0,z1,z2,z4,z653,z5,z6]),(0,[z654,z0,z1,z2,z4,z5,z6])],[(0,[z89,z0,z1,z2,z4,z5,z18]),(0,[z0,z14,z2,z4,z5,z6,z65]),(0,[z0,z1,z212,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z77]),(0,[z0,z1,z19,z8,z2,z4,z5]),(0,[z0,z1,z21,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z315,z18]),(0,[z0,z1,z446,z2,z4,z5,z6])],[(0,[z0,z14,z14,z2,z4,z5,z6]),(0,[z0,z1,z347,z2,z4,z5,z6]),(0,[z39,z0,z1,z2,z4,z5,z6]),(0,[z655,z0,z1,z2,z4,z5,z6]),(0,[z656,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z577]),(0,[z0,z1,z2,z4,z5,z20,z37]),(0,[z0,z1,z2,z4,z5,z239,z6]),(0,[z0,z1,z657,z2,z4,z5,z6])],[(0,[z0,z59,z2,z4,z5,z6,z277]),(0,[z171,z0,z2,z122,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z658,z6])]],
   [[(0,[z0,z14,z2,z40,z4,z5,z6]),(0,[z0,z14,z2,z117,z4,z5,z6]),(0,[z16,z0,z1,z2,z4,z5,z17]),(0,[z0,z1,z2,z4,z5,z659,z6]),(0,[z0,z1,z2,z4,z660,z5,z6]),(0,[z0,z1,z2,z4,z5,z34,z65])],[(0,[z0,z1,z661,z2,z4,z5,z6]),(1,[z0,z1,z292,z4,z5,z6]),(0,[z0,z1,z576,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z321,z6]),(0,[z0,z1,z2,z4,z5,z20,z155])],[(0,[z400,z0,z59,z2,z4,z5,z6]),(0,[z662,z0,z1,z2,z4,z5,z6]),(0,[z654,z0,z1,z2,z4,z5,z20])],[(0,[z0,z1,z2,z663,z4,z5,z6]),(0,[z0,z1,z2,z664,z4,z5,z6])],[(0,[z665,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z453,z5,z6]),(0,[z89,z16,z1,z2,z4,z5,z6]),(0,[z0,z149,z14,z2,z4,z5,z6]),(0,[z39,z0,z437,z2,z4,z5,z6]),(0,[z39,z0,z1,z2,z4,z5,z20]),(0,[z0,z1,z666,z2,z4,z5,z6]),(0,[z0,z667,z1,z2,z4,z5,z6])],[(0,[z0,z14,z2,z4,z5,z126,z6]),(1,[z71,z1,z2,z4,z135,z6]),(1,[z0,z1,z2,z4,z5,z541]),(0,[z0,z84,z2,z61,z4,z5,z6]),(0,[z0,z1,z8,z2,z4,z5,z6])],[(0,[z166,z1,z59,z2,z4,z5,z6]),(0,[z0,z59,z2,z4,z5,z6,z37]),(0,[z16,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z668,z2,z4,z5,z6]),(0,[z0,z1,z31,z2,z4,z5,z177])],[(0,[z0,z59,z2,z4,z32,z5,z6]),(0,[z89,z14,z1,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z5,z133,z6]),(0,[z669,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z54,z4,z110,z5,z6]),(0,[z0,z1,z2,z670,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z671,z5,z6]),(0,[z0,z1,z2,z4,z672,z5,z6]),(0,[z0,z1,z2,z4,z5,z673,z6]),(0,[z63,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z674,z5,z6])],[(0,[z633,z0,z59,z2,z4,z5,z6])],[(0,[z0,z14,z84,z2,z4,z5,z6]),(0,[z0,z1,z257,z2,z145,z4,z6]),(0,[z0,z1,z2,z4,z675,z5,z6]),(0,[z0,z1,z2,z4,z5,z676,z6]),(0,[z677,z0,z1,z2,z4,z5,z6])],[(1,[z0,z59,z2,z4,z5,z18]),(0,[z0,z14,z2,z4,z5,z33,z6]),(0,[z0,z1,z2,z52,z4,z5,z6]),(0,[z0,z1,z2,z678,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z88])],[(0,[z0,z1,z679,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z680,z6]),(0,[z0,z1,z2,z4,z681,z5,z6])],[(0,[z0,z14,z2,z4,z100,z5,z6])],[(0,[z0,z59,z2,z4,z79,z5,z6]),(0,[z98,z1,z2,z4,z5,z133,z6]),(0,[z0,z1,z2,z4,z5,z6,z682]),(0,[z0,z1,z2,z4,z5,z18,z96]),(0,[z0,z1,z2,z4,z5,z673,z20])],[(0,[z98,z0,z14,z2,z4,z5,z6]),(0,[z683,z0,z1,z2,z4,z5,z6]),(0,[z105,z1,z2,z40,z4,z5,z6]),(1,[z242,z0,z2,z4,z100,z6]),(1,[z64,z1,z2,z4,z5,z6]),(0,[z0,z1,z684,z2,z4,z5,z6]),(0,[z0,z685,z1,z2,z4,z5,z6])]],
   [[(0,[z166,z0,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z79,z5,z18]),(0,[z0,z1,z2,z686,z4,z5,z6]),(0,[z687,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z479,z5,z6]),(0,[z0,z1,z2,z4,z4,z5,z6]),(0,[z105,z0,z262,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z688,z5,z6]),(0,[z0,z1,z689,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z100,z126,z6]),(0,[z0,z1,z2,z4,z690,z5,z6]),(0,[z0,z1,z2,z66,z4,z5,z20]),(0,[z0,z1,z2,z691,z4,z5,z6]),(0,[z0,z1,z2,z692,z4,z5,z6])],[(1,[z16,z59,z2,z4,z5,z6]),(0,[z24,z0,z1,z2,z4,z5,z20]),(0,[z693,z0,z1,z2,z4,z5,z6]),(0,[z694,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z8,z2,z4,z5,z34])],[(0,[z16,z0,z1,z2,z4,z5,z34]),(0,[z0,z1,z2,z122,z4,z5,z577]),(0,[z0,z1,z2,z4,z5,z20,z6]),(0,[z499,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z90,z5,z18])],[(0,[z0,z1,z2,z4,z5,z6,z695]),(0,[z206,z0,z2,z4,z110,z5,z6])],[(0,[z0,z1,z696,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z697,z6]),(0,[z0,z1,z31,z119,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z698]),(0,[z0,z1,z511,z2,z4,z5,z6]),(0,[z0,z1,z699,z2,z4,z5,z6]),(0,[z0,z700,z1,z2,z4,z5,z6])],[(0,[z701,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z702,z6]),(0,[z0,z1,z2,z4,z5,z703,z6]),(0,[z0,z1,z2,z4,z5,z6,z704]),(1,[z0,z1,z8,z2,z4,z96])],[(0,[z0,z59,z2,z346,z4,z5,z6]),(0,[z105,z0,z14,z2,z4,z5,z6]),(1,[z0,z220,z84,z4,z5,z6]),(0,[z705,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z4,z5,z20]),(0,[z0,z1,z2,z4,z5,z6,z706])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z166,z398,z59,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z707])],[(0,[z0,z708,z2,z4,z5,z6]),(0,[z193,z14,z2,z4,z5,z6]),(0,[z251,z1,z2,z4,z5,z488])],[(0,[z398,z59,z2,z4,z79,z5]),(0,[z76,z0,z2,z4,z5,z401]),(0,[z0,z1,z2,z4,z709,z6])],[(0,[z105,z398,z59,z2,z4,z5]),(0,[z71,z59,z2,z4,z5,z18]),(0,[z0,z14,z2,z4,z5,z67])],[(0,[z0,z442,z2,z4,z5,z6]),(0,[z59,z2,z4,z554,z5,z6]),(0,[z76,z0,z398,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z710]),(0,[z105,z134,z2,z4,z5,z6]),(1,[z1,z2,z711,z5,z6]),(0,[z287,z1,z2,z4,z42,z6]),(0,[z0,z1,z712,z4,z5,z6])],[(0,[z1,z59,z202,z2,z4,z5]),(0,[z0,z1,z713,z2,z4,z5]),(0,[z0,z14,z2,z4,z5,z714]),(0,[z715,z1,z2,z4,z5,z6]),(0,[z0,z1,z651,z2,z126,z6])],[(0,[z59,z2,z4,z5,z395,z6]),(0,[z0,z59,z4,z5,z6,z88]),(0,[z0,z106,z2,z4,z5,z20]),(0,[z287,z1,z52,z4,z5,z6]),(0,[z716,z1,z2,z4,z5,z6])],[(0,[z0,z2,z4,z717,z5,z6])],[(0,[z262,z59,z2,z4,z5,z6]),(0,[z193,z59,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z328,z6]),(0,[z0,z1,z2,z4,z5,z718]),(0,[z0,z1,z2,z5,z20,z18])],[(0,[z0,z719,z59,z2,z4,z5]),(0,[z307,z14,z2,z4,z5,z6])],[(0,[z0,z1,z8,z2,z4,z360])],[(0,[z71,z398,z59,z2,z4,z5]),(0,[z0,z720,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z500]),(0,[z0,z721,z2,z4,z5,z6]),(0,[z0,z1,z2,z722,z5,z6])],[(0,[z76,z14,z59,z2,z4,z5]),(0,[z0,z437,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z77]),(0,[z723,z1,z2,z4,z5,z6])],[(0,[z76,z59,z2,z4,z41,z5]),(0,[z287,z84,z2,z4,z5,z6]),(0,[z0,z724,z2,z4,z5,z20])],[(0,[z0,z14,z2,z4,z5,z725]),(0,[z0,z14,z2,z4,z5,z44]),(1,[z0,z1,z31,z68,z4]),(0,[z0,z1,z2,z4,z90,z315])],[(0,[z13,z0,z2,z60,z5,z6]),(0,[z166,z245,z191,z4,z5,z6]),(0,[z71,z576,z2,z4,z135,z6]),(1,[z0,z1,z4,z5,z726])]],
   [[(0,[z245,z59,z2,z4,z5,z6]),(0,[z0,z1,z292,z4,z5,z6]),(0,[z0,z437,z2,z4,z5,z270]),(0,[z0,z1,z19,z4,z5,z224])],[(0,[z76,z59,z2,z4,z79,z5]),(0,[z13,z0,z2,z484,z5,z6]),(0,[z0,z1,z8,z2,z4,z196]),(0,[z0,z727,z2,z4,z5,z6])],[(0,[z59,z2,z4,z79,z5,z541]),(0,[z76,z265,z59,z2,z4,z5])],[(0,[z76,z16,z59,z2,z4,z5]),(0,[z0,z1,z53,z4,z5,z18])],[(0,[z497,z59,z2,z4,z5,z6]),(0,[z0,z1,z31,z4,z26,z6])],[(0,[z0,z59,z2,z4,z30,z6]),(0,[z0,z14,z2,z4,z5,z12]),(0,[z0,z728,z2,z4,z5,z6]),(0,[z0,z466,z2,z4,z5,z18]),(0,[z0,z1,z31,z4,z34,z33])],[(0,[z203,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z729]),(0,[z0,z1,z95,z8,z4,z96])],[(0,[z0,z730,z1,z2,z4,z5]),(0,[z71,z1,z626,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z731])],[(0,[z59,z2,z145,z4,z5,z20]),(0,[z0,z1,z2,z4,z732,z6]),(0,[z0,z1,z2,z4,z5,z733]),(0,[z543,z0,z2,z4,z100,z6])],[(0,[z0,z1,z511,z11,z35,z6])],[(0,[z0,z1,z2,z4,z5,z734])],[(0,[z0,z59,z2,z4,z5,z281]),(0,[z39,z1,z2,z41,z5,z270]),(0,[z0,z1,z31,z612,z4,z6]),(0,[z735,z1,z2,z4,z5,z6]),(0,[z0,z1,z31,z68,z4,z6]),(0,[z0,z736,z2,z4,z5,z6])],[(0,[z166,z737,z2,z4,z5,z6]),(0,[z0,z59,z356,z4,z5,z6]),(0,[z59,z2,z4,z79,z126,z6]),(0,[z0,z256,z2,z160,z5,z6]),(0,[z203,z1,z2,z4,z5,z20]),(0,[z0,z2,z4,z5,z738,z37])],[(0,[z307,z1,z2,z4,z30,z6]),(0,[z739,z1,z2,z4,z5,z18])],[(0,[z64,z1,z2,z4,z5,z6]),(0,[z568,z59,z145,z4,z5,z6]),(0,[z0,z1,z740,z4,z5,z6]),(0,[z0,z14,z2,z4,z5,z741]),(0,[z242,z0,z2,z4,z100,z6])],[(0,[z0,z742,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z743]),(0,[z0,z1,z744,z2,z4,z5])]],
   [[(0,[z480,z1,z2,z4,z79,z6]),(0,[z0,z1,z745,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z746]),(0,[z265,z201,z2,z4,z5,z6])],[(0,[z0,z142,z2,z4,z5,z6]),(0,[z0,z59,z747,z2,z4,z6]),(0,[z483,z59,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z6,z748]),(0,[z0,z1,z749,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z115]),(0,[z0,z1,z2,z4,z672,z34])],[(0,[z0,z1,z356,z4,z328,z6]),(0,[z0,z1,z54,z110,z5,z6])],[(0,[z59,z145,z4,z110,z5,z6]),(0,[z633,z1,z145,z4,z5,z6]),(0,[z0,z1,z2,z4,z750,z6]),(0,[z123,z2,z145,z4,z5,z6]),(0,[z0,z1,z751,z4,z5,z6]),(0,[z242,z0,z2,z4,z100,z20]),(0,[z0,z1,z94,z2,z4,z6])],[(0,[z0,z59,z2,z4,z5,z187])],[(0,[z175,z0,z2,z479,z5,z6]),(0,[z0,z752,z2,z4,z5,z6]),(0,[z57,z1,z2,z4,z79,z6]),(0,[z0,z1,z2,z4,z5,z753]),(0,[z0,z1,z754,z4,z5,z18])],[(0,[z0,z142,z2,z4,z5,z20]),(0,[z13,z287,z2,z269,z5,z6])],[(1,[z0,z1,z4,z755,z6]),(0,[z0,z1,z2,z4,z5,z756])],[(0,[z59,z2,z4,z5,z624,z6]),(0,[z633,z0,z361,z4,z5,z6]),(0,[z0,z59,z2,z4,z5,z757]),(0,[z89,z466,z2,z4,z5,z6]),(0,[z0,z14,z312,z2,z4,z5]),(0,[z0,z1,z54,z110,z5,z20])],[(0,[z0,z262,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z5,z341]),(0,[z561,z1,z2,z4,z135,z6]),(0,[z0,z1,z758,z2,z4,z5]),(0,[z0,z1,z94,z2,z4,z20]),(1,[z0,z1,z2,z4,z759])],[(0,[z425,z59,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z760,z6])],[(0,[z473,z14,z2,z4,z5,z6]),(0,[z57,z1,z2,z4,z79,z20]),(0,[z761,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z762]),(0,[z0,z1,z2,z11,z763,z6])],[(1,[z59,z202,z2,z4,z5]),(0,[z156,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z764])],[(0,[z0,z256,z2,z122,z5,z18])],[(0,[z0,z1,z257,z202,z2,z4]),(0,[z0,z1,z119,z172,z5,z6])]],
   [[(0,[z0,z262,z2,z4,z5,z20]),(0,[z0,z1,z2,z188,z5,z18])],[(0,[z124,z0,z376,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z765]),(0,[z0,z1,z766,z2,z4,z6]),(0,[z0,z2,z4,z5,z738,z6])],[(0,[z76,z265,z1,z2,z4,z5]),(0,[z0,z72,z2,z4,z5,z18])],[(0,[z76,z16,z1,z2,z4,z5]),(0,[z0,z1,z767,z4,z5,z6]),(0,[z0,z1,z2,z4,z42,z6]),(0,[z0,z1,z2,z4,z5,z81]),(0,[z0,z1,z2,z4,z5,z768])],[(0,[z16,z59,z9,z2,z4,z5]),(0,[z59,z513,z2,z4,z5,z6]),(0,[z16,z372,z2,z4,z5,z17]),(0,[z0,z1,z31,z4,z150,z6])],[(0,[z0,z1,z52,z4,z5,z6]),(0,[z0,z1,z2,z5,z6,z769])],[(0,[z63,z0,z398,z2,z4,z5]),(0,[z0,z1,z770,z2,z5,z6]),(0,[z105,z1,z2,z642,z5,z6]),(0,[z0,z771,z2,z4,z5,z6])],[(0,[z0,z14,z119,z66,z5,z6]),(0,[z0,z1,z2,z4,z5,z772]),(0,[z0,z1,z68,z4,z32,z5])],[(0,[z0,z1,z2,z4,z5,z773]),(0,[z138,z1,z2,z4,z5,z17]),(0,[z0,z1,z2,z774,z5,z6]),(0,[z0,z1,z31,z19,z8,z4])],[(0,[z0,z59,z257,z2,z4,z6]),(0,[z0,z1,z2,z4,z297,z20]),(0,[z417,z2,z4,z100,z5,z6])],[(0,[z166,z59,z145,z4,z5,z6]),(0,[z98,z14,z2,z4,z5,z133]),(0,[z287,z1,z2,z4,z5,z232]),(0,[z0,z1,z2,z35,z763,z6])],[(0,[z166,z59,z2,z4,z5,z18]),(0,[z0,z59,z237,z2,z5,z18]),(0,[z0,z1,z2,z4,z5,z775]),(0,[z0,z1,z2,z4,z776,z6]),(0,[z0,z452,z2,z4,z136,z6]),(0,[z0,z1,z95,z8,z4,z6])],[(0,[z0,z107,z2,z4,z5,z6]),(0,[z0,z219,z388,z4,z5,z6]),(0,[z0,z99,z2,z4,z136,z18])],[(0,[z59,z312,z2,z145,z4,z5]),(0,[z0,z14,z95,z4,z5,z6]),(0,[z0,z14,z53,z4,z5,z6]),(0,[z0,z134,z2,z4,z5,z18])],[(0,[z105,z59,z2,z4,z5,z18]),(0,[z0,z59,z2,z4,z90,z34]),(0,[z59,z2,z4,z5,z530,z6]),(0,[z0,z1,z202,z2,z4,z5]),(0,[z338,z242,z2,z4,z100,z6]),(0,[z0,z777,z2,z4,z5,z6])],[]],
   [[(0,[z16,z59,z19,z2,z4,z5]),(0,[z1,z2,z778,z4,z5,z6]),(0,[z71,z72,z2,z4,z135,z6]),(0,[z0,z84,z779,z4,z5,z6]),(0,[z780,z0,z2,z4,z5,z6])],[(0,[z398,z59,z2,z4,z41,z5]),(0,[z89,z14,z2,z4,z5,z18]),(0,[z39,z14,z2,z41,z5,z6]),(0,[z24,z1,z257,z145,z4,z6]),(0,[z0,z134,z2,z4,z5,z270]),(0,[z0,z1,z781,z4,z5,z6]),(0,[z0,z1,z2,z4,z385,z18]),(0,[z0,z1,z95,z8,z4,z5])],[(0,[z0,z59,z2,z4,z782,z5]),(0,[z0,z1,z2,z5,z20,z249]),(0,[z0,z1,z2,z4,z263,z18]),(0,[z0,z1,z2,z4,z20,z86])],[(0,[z0,z106,z2,z4,z5,z6]),(0,[z0,z1,z4,z755,z239,z6]),(0,[z783,z1,z2,z4,z5,z6])],[(0,[z0,z568,z268,z4,z5,z6]),(0,[z0,z437,z2,z4,z328,z6]),(0,[z0,z576,z2,z4,z5,z18]),(0,[z784,z1,z2,z4,z5,z6])],[(0,[z63,z16,z59,z2,z4,z5]),(0,[z0,z1,z356,z4,z5,z341]),(0,[z0,z1,z2,z4,z5,z785]),(0,[z0,z1,z786,z2,z4,z5]),(0,[z0,z1,z4,z517,z5,z18])],[(0,[z16,z787,z2,z4,z5,z6]),(0,[z89,z72,z2,z4,z5,z6]),(0,[z13,z0,z2,z269,z5,z6]),(0,[z338,z1,z2,z4,z5,z20])],[(0,[z59,z2,z4,z79,z5,z18]),(0,[z59,z2,z686,z4,z5,z6]),(0,[z0,z788,z2,z4,z5,z6])],[(0,[z76,z59,z2,z145,z4,z5]),(0,[z59,z2,z4,z688,z5,z6]),(0,[z59,z2,z691,z4,z5,z6]),(0,[z0,z14,z2,z4,z5,z789]),(0,[z105,z1,z2,z40,z5,z18])],[(0,[z572,z59,z2,z4,z5,z6]),(0,[z16,z1,z2,z4,z5,z340]),(0,[z0,z1,z2,z790,z5,z6]),(0,[z0,z1,z2,z4,z791,z6]),(0,[z13,z0,z2,z269,z5,z232]),(0,[z0,z1,z2,z4,z5,z792]),(0,[z0,z1,z2,z4,z793,z5]),(0,[z0,z1,z2,z4,z759,z96])],[(0,[z0,z14,z48,z4,z32,z6]),(0,[z0,z724,z2,z4,z5,z6]),(0,[z16,z1,z2,z4,z5,z17]),(0,[z206,z794,z2,z4,z5,z6]),(0,[z0,z1,z795,z2,z4,z6]),(0,[z796,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z797]),(0,[z0,z1,z2,z4,z5,z798]),(0,[z0,z1,z2,z4,z5,z738])],[(0,[z0,z1,z2,z4,z799,z6]),(0,[z0,z1,z2,z4,z5,z800]),(0,[z13,z0,z2,z269,z5,z20])],[(0,[z0,z59,z2,z4,z5,z801]),(0,[z0,z59,z2,z4,z5,z67]),(1,[z0,z1,z19,z94,z4])],[(0,[z0,z1,z174,z2,z4,z481])],[(0,[z0,z14,z2,z4,z5,z439])]],
   [[(0,[z0,z372,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z802,z6]),(0,[z0,z2,z122,z803,z5,z6]),(0,[z0,z1,z119,z66,z5,z18]),(0,[z0,z1,z2,z4,z5,z804]),(0,[z0,z805,z2,z4,z5,z18]),(0,[z796,z1,z2,z4,z5,z20])],[(0,[z448,z59,z2,z4,z5,z6]),(0,[z59,z573,z2,z4,z5,z6]),(0,[z14,z195,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z806,z6]),(0,[z0,z437,z356,z4,z5,z6]),(0,[z0,z1,z53,z4,z30,z6]),(0,[z0,z1,z2,z4,z5,z177])],[(0,[z0,z59,z2,z4,z328,z6]),(0,[z0,z1,z312,z212,z2,z4]),(0,[z807,z1,z2,z4,z5,z6])],[(0,[z0,z59,z808,z4,z5,z6]),(0,[z307,z59,z2,z4,z5,z6]),(0,[z0,z809,z2,z4,z5,z6])],[(0,[z0,z810,z2,z4,z5,z6])],[(0,[z59,z2,z145,z4,z5,z6]),(0,[z0,z811,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z812])],[(0,[z0,z1,z813,z2,z4,z5]),(0,[z0,z372,z2,z4,z5,z20]),(0,[z0,z1,z19,z4,z5,z399]),(0,[z0,z1,z95,z4,z5,z18])],[(0,[z0,z59,z814,z4,z5,z6]),(0,[z493,z59,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z5,z815]),(0,[z0,z1,z2,z4,z816,z6]),(0,[z0,z1,z2,z4,z5,z199]),(0,[z0,z1,z21,z2,z126,z22]),(0,[z0,z1,z2,z11,z35,z18])],[(0,[z0,z59,z2,z4,z5,z44]),(0,[z0,z1,z2,z4,z817,z6]),(0,[z818,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z819]),(0,[z820,z1,z2,z4,z5,z6])],[(0,[z0,z1,z254,z110,z5,z6])],[(0,[z39,z1,z2,z41,z5,z18]),(0,[z0,z1,z4,z5,z6,z726])],[(0,[z0,z821,z2,z4,z5,z6])],[(0,[z0,z59,z2,z4,z822,z5])],[(0,[z0,z1,z823,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z824]),(0,[z0,z825,z2,z4,z5,z6]),(0,[z0,z826,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z827]),(0,[z820,z1,z2,z4,z5,z20])],[(0,[z0,z59,z2,z4,z5,z12])]],
   [[(0,[z0,z1,z2,z4,z828,z6])],[(0,[z0,z1,z2,z4,z829,z6]),(0,[z0,z442,z2,z4,z5,z18])],[(0,[z0,z1,z119,z302,z5,z6]),(0,[z0,z1,z2,z4,z5,z830]),(0,[z0,z1,z4,z831,z5,z6])],[(0,[z59,z2,z4,z5,z615,z6]),(0,[z1,z2,z4,z832,z135,z6]),(0,[z0,z1,z2,z4,z30,z439]),(0,[z0,z256,z2,z803,z5,z6]),(0,[z0,z1,z48,z4,z32,z18])],[(0,[z0,z14,z2,z4,z5,z224]),(0,[z0,z54,z143,z110,z5,z6])],[(0,[z0,z59,z833,z2,z5,z6]),(0,[z0,z1,z2,z4,z834,z6]),(0,[z57,z1,z2,z4,z832,z6]),(0,[z63,z0,z372,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z835]),(0,[z654,z0,z2,z4,z5,z216]),(0,[z0,z1,z48,z4,z6,z478]),(0,[z0,z1,z2,z4,z5,z22])],[(0,[z0,z437,z2,z4,z5,z341]),(0,[z0,z836,z106,z2,z4,z5]),(0,[z417,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z828,z20])],[(0,[z166,z59,z191,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z837]),(0,[z838,z1,z2,z4,z5,z6])],[(0,[z71,z107,z2,z4,z5,z6]),(0,[z0,z839,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z840]),(0,[z1,z2,z4,z5,z760,z17]),(0,[z0,z1,z2,z579,z5,z20])],[(0,[z0,z2,z779,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z232]),(0,[z841,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z339,z5,z18]),(0,[z0,z1,z2,z4,z5,z842]),(0,[z0,z843,z2,z4,z5,z6])],[(0,[z59,z2,z4,z35,z79,z6]),(0,[z0,z14,z2,z4,z385,z6]),(0,[z0,z1,z2,z4,z173,z34])],[(0,[z0,z1,z2,z4,z5,z20]),(0,[z59,z626,z2,z4,z5,z6]),(0,[z0,z719,z1,z2,z4,z5]),(0,[z0,z14,z2,z4,z263,z6]),(0,[z0,z1,z2,z4,z5,z844])],[(0,[z0,z1,z292,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z845]),(0,[z0,z1,z2,z4,z5,z846])],[(0,[z0,z14,z2,z4,z5,z577])],[(0,[z59,z2,z141,z4,z5,z6]),(0,[z0,z14,z4,z517,z5,z6]),(0,[z0,z1,z2,z515,z5,z18]),(0,[z0,z1,z2,z4,z6,z847])]],
   [[(0,[z59,z2,z4,z5,z636,z6]),(0,[z0,z843,z2,z4,z5,z20])],[(0,[z0,z1,z292,z4,z5,z270]),(0,[z0,z1,z2,z4,z5,z848]),(0,[z0,z849,z2,z4,z5,z6])],[(0,[z0,z59,z2,z4,z385,z6]),(0,[z89,z708,z2,z4,z5,z6]),(0,[z105,z14,z2,z40,z5,z6]),(0,[z850,z0,z2,z4,z5,z6]),(0,[z0,z1,z851,z4,z5,z6]),(0,[z0,z1,z2,z261,z5,z20])],[(0,[z0,z59,z312,z2,z4,z5]),(0,[z0,z1,z95,z4,z90,z5])],[(0,[z0,z25,z2,z4,z5,z6]),(0,[z0,z59,z2,z4,z5,z341]),(0,[z0,z14,z68,z2,z4,z5]),(0,[z0,z1,z2,z4,z385,z67]),(0,[z0,z1,z19,z4,z86,z65]),(0,[z0,z1,z94,z2,z4,z34])],[(0,[z0,z1,z257,z119,z4,z6])],[(0,[z253,z1,z191,z4,z5,z6]),(0,[z0,z1,z2,z4,z297,z6])],[(0,[z0,z1,z2,z4,z5,z852]),(0,[z0,z1,z2,z4,z853,z6]),(0,[z854,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z855,z5,z6]),(0,[z0,z1,z2,z4,z5,z856])],[(0,[z0,z1,z343,z2,z5,z18]),(0,[z0,z1,z8,z617,z2,z4])],[(0,[z59,z2,z4,z5,z658,z6]),(0,[z0,z1,z857,z4,z5,z6]),(0,[z858,z1,z2,z4,z5,z6])],[(0,[z59,z2,z179,z4,z5,z6]),(0,[z287,z1,z2,z4,z5,z6]),(0,[z0,z25,z2,z4,z5,z20]),(0,[z24,z1,z145,z4,z5,z20]),(0,[z0,z2,z4,z143,z5,z20])],[(0,[z0,z1,z2,z4,z328,z341]),(0,[z242,z0,z2,z4,z100,z18]),(0,[z64,z1,z2,z4,z5,z18]),(0,[z0,z1,z54,z110,z5,z321])],[(0,[z398,z59,z2,z145,z4,z5]),(0,[z0,z859,z2,z4,z5,z6])],[(0,[z737,z59,z2,z4,z5,z6]),(0,[z0,z99,z2,z4,z104,z6]),(0,[z0,z1,z2,z4,z5,z860]),(0,[z16,z1,z509,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z861])],[(0,[z0,z1,z2,z4,z5,z862]),(0,[z0,z1,z8,z2,z4,z224]),(0,[z1,z2,z4,z5,z18,z863])],[(0,[z0,z14,z2,z4,z864,z6]),(0,[z0,z1,z2,z4,z865,z6])]],
   [[(0,[z0,z1,z866,z2,z4,z6]),(0,[z287,z1,z2,z4,z5,z20])],[(0,[z0,z59,z119,z66,z5,z6]),(0,[z0,z14,z9,z4,z5,z33]),(0,[z0,z14,z2,z11,z35,z6])],[(0,[z59,z2,z4,z205,z5,z6]),(0,[z59,z207,z2,z4,z5,z6]),(0,[z24,z25,z145,z4,z5,z6]),(0,[z0,z134,z356,z4,z5,z6]),(0,[z0,z867,z2,z4,z5,z6]),(0,[z0,z1,z282,z4,z5,z399])],[(0,[z338,z1,z2,z4,z5,z6]),(0,[z868,z203,z1,z2,z4,z5]),(0,[z0,z1,z119,z66,z5,z67])],[(0,[z59,z257,z2,z145,z4,z6]),(0,[z98,z59,z2,z4,z5,z133]),(0,[z0,z220,z779,z4,z5,z6])],[(0,[z0,z869,z2,z4,z5,z6])],[],[(0,[z0,z59,z95,z4,z5,z6]),(0,[z0,z59,z53,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z870]),(0,[z0,z1,z2,z280,z5,z18]),(0,[z0,z1,z871,z4,z5,z6])],[(0,[z0,z59,z9,z4,z5,z33]),(0,[z0,z1,z2,z872,z5,z6])],[(0,[z0,z873,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z874]),(0,[z0,z875,z2,z4,z5,z6]),(0,[z0,z1,z4,z517,z5,z281])],[(0,[z0,z59,z2,z4,z5,z876]),(0,[z631,z59,z2,z4,z5,z6]),(0,[z0,z316,z2,z4,z5,z296]),(0,[z0,z1,z9,z4,z5,z218])],[(0,[z39,z59,z2,z41,z5,z6]),(0,[z0,z1,z2,z4,z877,z5]),(0,[z0,z1,z2,z4,z878,z5]),(0,[z0,z1,z2,z4,z5,z879]),(0,[z0,z1,z511,z4,z5,z20])],[(0,[z0,z1,z880,z2,z4,z6]),(0,[z13,z0,z2,z803,z5,z6])],[(0,[z0,z1,z2,z4,z5,z881])],[],[(0,[z0,z14,z2,z5,z20,z18]),(0,[z0,z1,z2,z4,z5,z882]),(0,[z868,z0,z1,z2,z4,z5]),(0,[z307,z1,z53,z4,z5,z6])]],
   [[(0,[z0,z398,z372,z2,z4,z5]),(0,[z0,z1,z603,z2,z126,z6]),(0,[z0,z1,z2,z4,z42,z18]),(0,[z0,z1,z4,z110,z385,z6])],[(0,[z0,z883,z2,z4,z5,z6]),(0,[z57,z1,z2,z4,z79,z541]),(0,[z0,z1,z884,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z759])],[(0,[z0,z1,z885,z4,z5,z6]),(0,[z0,z14,z2,z4,z5,z500]),(0,[z39,z1,z2,z41,z328,z6]),(0,[z886,z1,z2,z4,z5,z6]),(0,[z0,z1,z52,z4,z5,z18])],[(0,[z0,z14,z2,z4,z5,z77]),(0,[z0,z887,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z888]),(0,[z0,z1,z2,z4,z5,z889])],[(0,[z0,z59,z48,z4,z32,z6]),(0,[z0,z1,z9,z4,z5,z323]),(0,[z0,z890,z2,z4,z5,z6])],[(0,[z316,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z891]),(0,[z0,z892,z2,z4,z5,z6])],[(0,[z0,z1,z2,z189,z5,z20]),(0,[z0,z1,z2,z893,z5,z6]),(0,[z0,z894,z2,z4,z5,z6]),(0,[z0,z1,z895,z4,z5,z6])],[(0,[z0,z14,z292,z4,z5,z6]),(0,[z0,z1,z2,z635,z5,z18]),(0,[z0,z1,z2,z4,z896,z6]),(0,[z0,z1,z2,z5,z20,z474])],[(0,[z1,z59,z2,z4,z5,z541]),(0,[z0,z1,z897,z4,z5,z6]),(0,[z0,z1,z8,z4,z88,z96])],[(0,[z0,z59,z2,z4,z5,z439]),(0,[z0,z107,z2,z4,z5,z18])],[(0,[z0,z1,z2,z4,z5,z898]),(0,[z0,z1,z2,z4,z5,z899]),(0,[z98,z318,z2,z4,z5,z133]),(0,[z0,z1,z2,z4,z900,z6]),(0,[z0,z1,z2,z4,z5,z901])],[(0,[z0,z1,z2,z4,z902,z6]),(0,[z0,z1,z21,z2,z126,z6]),(0,[z0,z1,z2,z11,z35,z281]),(0,[z0,z1,z430,z4,z5,z218])],[(0,[z73,z59,z2,z4,z5,z6]),(1,[z0,z2,z803,z5,z6]),(0,[z0,z903,z2,z4,z5,z6])],[(0,[z203,z14,z2,z4,z5,z6]),(0,[z287,z2,z4,z269,z5,z6])],[(0,[z0,z1,z2,z4,z5,z904]),(0,[z0,z1,z2,z4,z5,z905])],[(0,[z400,z59,z2,z4,z5,z20]),(0,[z175,z59,z2,z41,z5,z6]),(0,[z0,z787,z2,z4,z5,z6]),(0,[z0,z906,z2,z4,z5,z6]),(0,[z39,z1,z356,z41,z5,z6]),(1,[z1,z2,z4,z5,z760]),(0,[z0,z1,z66,z831,z5,z6]),(0,[z0,z1,z2,z4,z5,z907])]],
   [[(0,[z0,z59,z2,z908,z4,z6]),(0,[z0,z106,z2,z4,z5,z18]),(0,[z0,z1,z668,z2,z5,z18]),(0,[z0,z1,z31,z4,z239,z177])],[(0,[z0,z1,z2,z4,z5,z909]),(0,[z0,z1,z910,z4,z5,z6]),(0,[z307,z1,z2,z4,z5,z439]),(0,[z0,z911,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z912]),(0,[z0,z1,z21,z2,z126,z20])],[(0,[z0,z1,z2,z4,z5,z913])],[(0,[z417,z1,z2,z4,z5,z6]),(0,[z0,z1,z31,z4,z187,z239])],[],[(0,[z64,z14,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z914])],[(0,[z0,z1,z4,z915,z5,z6]),(0,[z0,z201,z372,z2,z4,z5]),(1,[z0,z1,z95,z8,z4]),(0,[z0,z1,z2,z4,z34,z759])],[(0,[z59,z2,z4,z5,z320,z6]),(0,[z0,z347,z2,z4,z5,z20]),(0,[z0,z1,z916,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z917])],[(0,[z71,z76,z59,z2,z4,z5]),(0,[z1,z2,z40,z711,z5,z6]),(0,[z0,z1,z19,z4,z5,z65]),(0,[z0,z1,z4,z5,z18,z88])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z5,z115]),(0,[z0,z14,z2,z4,z5,z918]),(0,[z648,z1,z2,z4,z79,z6]),(0,[z203,z219,z2,z4,z5,z6]),(0,[z0,z1,z2,z763,z126,z6])],[(0,[z468,z59,z2,z4,z5,z6]),(0,[z0,z14,z54,z110,z5,z6]),(0,[z0,z1,z919,z4,z5,z6])],[(0,[z0,z14,z2,z4,z750,z6]),(0,[z0,z14,z94,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z920]),(0,[z654,z0,z2,z4,z5,z673])],[(1,[z1,z778,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z443]),(0,[z0,z1,z2,z4,z5,z921]),(0,[z0,z1,z831,z110,z5,z6]),(0,[z0,z1,z2,z4,z6,z86])],[(0,[z278,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z922,z6]),(0,[z0,z923,z2,z4,z5,z6]),(0,[z0,z1,z2,z230,z5,z20]),(0,[z0,z1,z779,z4,z5,z6]),(0,[z0,z924,z2,z4,z5,z6])],[(0,[z708,z1,z2,z4,z5,z6]),(0,[z0,z59,z2,z4,z5,z224]),(0,[z1,z778,z145,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z925]),(0,[z0,z1,z2,z653,z5,z18])],[(0,[z0,z926,z2,z4,z5,z6]),(0,[z0,z59,z4,z927,z5,z6]),(0,[z0,z1,z212,z2,z4,z6])]],
   [[(0,[z0,z1,z210,z4,z5,z33])],[(0,[z76,z400,z59,z2,z4,z5]),(0,[z0,z928,z2,z4,z5,z6])],[(0,[z59,z2,z145,z4,z5,z18]),(0,[z0,z2,z4,z929,z5,z6]),(0,[z0,z1,z2,z5,z659,z18]),(0,[z0,z1,z2,z930,z5,z6])],[(0,[z0,z1,z2,z931,z4,z5]),(0,[z932,z1,z2,z4,z5,z6])],[(0,[z0,z59,z933,z2,z4,z5]),(0,[z39,z1,z2,z41,z5,z341])],[(0,[z934,z59,z2,z4,z5,z6]),(0,[z0,z1,z212,z2,z4,z20]),(0,[z16,z1,z2,z4,z5,z530]),(0,[z0,z1,z31,z4,z239,z6])],[(0,[z580,z59,z2,z4,z5,z6]),(0,[z0,z59,z2,z4,z263,z6]),(0,[z203,z1,z2,z4,z5,z18])],[(0,[z316,z398,z59,z2,z4,z5]),(0,[z0,z1,z935,z4,z5,z6]),(0,[z24,z1,z145,z4,z5,z6]),(0,[z0,z2,z4,z143,z5,z6])],[(0,[z0,z59,z2,z4,z5,z577]),(0,[z0,z134,z2,z4,z328,z6]),(0,[z0,z1,z2,z4,z5,z936]),(0,[z0,z1,z2,z4,z5,z937]),(0,[z206,z0,z61,z4,z5,z6]),(0,[z0,z1,z2,z4,z263,z67])],[(0,[z71,z59,z48,z2,z4,z6]),(0,[z16,z59,z2,z4,z5,z96]),(0,[z0,z59,z4,z517,z5,z6])],[(0,[z0,z14,z2,z4,z5,z81]),(0,[z0,z14,z2,z4,z42,z6])],[(0,[z0,z1,z2,z4,z938,z6]),(0,[z0,z1,z31,z4,z239,z20]),(0,[z0,z1,z2,z276,z5,z20])],[(0,[z105,z59,z2,z40,z5,z6]),(0,[z561,z59,z2,z4,z5,z6]),(0,[z0,z14,z52,z4,z5,z6]),(0,[z171,z0,z61,z4,z5,z20]),(0,[z0,z2,z4,z5,z939,z6]),(0,[z0,z1,z2,z4,z5,z940])],[(0,[z941,z59,z2,z4,z5,z6]),(0,[z942,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z943])],[(0,[z253,z59,z2,z4,z5,z6]),(0,[z0,z59,z68,z2,z4,z5]),(0,[z24,z1,z312,z145,z4,z5]),(0,[z0,z1,z2,z4,z832,z6]),(0,[z0,z1,z2,z4,z5,z321])],[(1,[z0,z2,z4,z944,z6])]],
   [[(1,[z59,z2,z4,z5,z541]),(0,[z0,z1,z257,z312,z2,z4]),(0,[z39,z437,z2,z41,z5,z6]),(0,[z0,z1,z2,z4,z5,z945])],[(0,[z469,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z946]),(0,[z0,z142,z2,z4,z5,z18])],[(0,[z59,z391,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z776,z6]),(0,[z0,z1,z2,z4,z947,z6]),(0,[z0,z1,z2,z4,z20,z948])],[(0,[z364,z59,z2,z41,z5,z6]),(0,[z0,z1,z949,z2,z5,z6]),(0,[z0,z950,z2,z4,z5,z6]),(0,[z0,z1,z951,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z952]),(0,[z0,z1,z54,z110,z5,z18])],[(0,[z171,z193,z61,z4,z5,z6]),(0,[z0,z1,z94,z2,z4,z18])],[(0,[z953,z0,z59,z2,z4,z5]),(0,[z621,z59,z2,z4,z5,z6]),(0,[z0,z14,z202,z2,z4,z5]),(0,[z954,z1,z2,z4,z5,z6])],[(0,[z57,z1,z2,z4,z79,z18])],[(0,[z0,z1,z48,z494,z4,z6]),(0,[z955,z1,z2,z4,z5,z6])],[(0,[z59,z410,z2,z4,z5,z6]),(0,[z656,z14,z2,z4,z5,z6]),(0,[z0,z956,z2,z4,z5,z6]),(0,[z0,z1,z511,z4,z5,z6]),(0,[z0,z1,z4,z32,z6,z424])],[(0,[z59,z2,z4,z5,z412,z6]),(0,[z0,z1,z2,z4,z5,z957]),(0,[z0,z2,z803,z269,z5,z6]),(0,[z0,z1,z2,z4,z18,z958])],[(0,[z532,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z959]),(0,[z0,z1,z2,z4,z960,z6]),(0,[z0,z262,z2,z4,z5,z18]),(0,[z0,z1,z119,z831,z5,z6])],[(0,[z0,z59,z2,z11,z35,z6]),(0,[z264,z0,z2,z4,z5,z23]),(0,[z961,z417,z1,z2,z4,z5]),(0,[z63,z0,z2,z4,z5,z423]),(0,[z0,z1,z4,z5,z20,z88])],[],[(0,[z59,z2,z4,z5,z133,z6]),(0,[z0,z1,z2,z4,z5,z962]),(0,[z0,z1,z4,z517,z5,z12])],[(0,[z59,z2,z240,z4,z5,z6]),(0,[z963,z1,z2,z4,z5,z6]),(0,[z0,z964,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z562,z34])],[(0,[z0,z1,z965,z2,z4,z6]),(0,[z0,z2,z4,z803,z5,z6])]],
   [[(0,[z76,z59,z2,z4,z5,z133]),(0,[z600,z14,z2,z4,z5,z6]),(0,[z0,z1,z52,z4,z30,z6]),(0,[z0,z1,z2,z831,z5,z6])],[(0,[z16,z14,z2,z4,z5,z17]),(0,[z0,z1,z2,z4,z5,z541])],[(0,[z0,z1,z2,z4,z86,z18])],[(0,[z0,z437,z292,z4,z5,z6]),(0,[z0,z1,z2,z4,z297,z18])],[(0,[z0,z364,z2,z346,z5,z6]),(0,[z206,z0,z54,z110,z5,z6]),(0,[z966,z1,z2,z4,z5,z6])],[(0,[z0,z1,z967,z2,z4,z5]),(0,[z0,z1,z53,z4,z5,z439])],[(0,[z0,z59,z713,z2,z4,z5]),(0,[z131,z59,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z297,z270]),(0,[z0,z1,z2,z4,z5,z968]),(0,[z71,z1,z2,z4,z135,z20]),(0,[z287,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z969])],[(0,[z0,z14,z2,z4,z5,z177]),(0,[z39,z1,z2,z711,z5,z6]),(0,[z0,z1,z970,z2,z4,z5])],[(0,[z0,z59,z2,z5,z20,z18])],[(0,[z0,z290,z2,z4,z136,z6]),(0,[z0,z1,z971,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z972]),(0,[z973,z0,z2,z4,z5,z6]),(0,[z0,z134,z2,z4,z5,z341]),(0,[z0,z974,z2,z4,z5,z6]),(0,[z0,z1,z446,z4,z5,z65])],[(0,[z1,z2,z711,z41,z5,z6]),(0,[z0,z975,z2,z4,z5,z6])],[(0,[z400,z59,z2,z4,z5,z6]),(0,[z0,z59,z2,z4,z5,z500]),(0,[z59,z2,z4,z460,z5,z6]),(0,[z976,z0,z106,z2,z4,z5])],[(0,[z0,z59,z2,z4,z5,z77]),(0,[z0,z1,z2,z4,z5,z977]),(0,[z794,z1,z2,z4,z5,z6])],[(0,[z89,z262,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z5,z199]),(0,[z0,z1,z2,z4,z5,z978]),(0,[z0,z979,z2,z4,z5,z6])],[(0,[z0,z1,z2,z11,z35,z12]),(0,[z980,z1,z2,z4,z5,z6])]],
   [[(0,[z338,z1,z2,z4,z5,z18]),(0,[z0,z1,z95,z4,z5,z33])],[(0,[z14,z59,z2,z4,z5,z6]),(0,[z0,z59,z292,z4,z5,z6]),(0,[z13,z0,z2,z269,z30,z6])],[(0,[z28,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z981,z4,z5]),(0,[z0,z836,z1,z2,z4,z5]),(0,[z982,z1,z2,z4,z5,z6])],[(0,[z983,z1,z2,z4,z5,z6]),(0,[z984,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z985])],[(0,[z16,z59,z2,z4,z5,z20]),(0,[z0,z347,z2,z4,z5,z6]),(0,[z0,z1,z2,z986,z5,z6]),(0,[z0,z2,z4,z987,z5,z6]),(0,[z171,z0,z52,z4,z5,z6]),(0,[z0,z1,z988,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z989]),(0,[z953,z0,z1,z2,z4,z5]),(0,[z0,z990,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z33,z82])],[(0,[z206,z0,z52,z4,z5,z6]),(0,[z13,z0,z2,z269,z5,z18]),(0,[z0,z1,z2,z4,z5,z991])],[(0,[z149,z59,z2,z4,z5,z6]),(0,[z14,z59,z2,z4,z5,z20]),(0,[z203,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z992]),(0,[z0,z1,z2,z4,z993,z6])],[(0,[z514,z0,z2,z60,z5,z6]),(0,[z0,z1,z292,z4,z328,z6])],[(0,[z0,z1,z994,z2,z4,z5]),(0,[z0,z220,z84,z4,z5,z20]),(0,[z0,z995,z2,z4,z5,z6]),(0,[z0,z996,z2,z4,z5,z6])],[(0,[z71,z1,z2,z4,z832,z6]),(0,[z64,z466,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z997]),(0,[z0,z1,z95,z4,z5,z224]),(0,[z0,z1,z795,z2,z4,z18])],[(0,[z0,z1,z119,z66,z385,z6])],[(0,[z0,z14,z2,z4,z5,z22]),(0,[z0,z1,z2,z75,z5,z18])],[(0,[z59,z2,z4,z41,z5,z6]),(0,[z14,z450,z2,z4,z5,z6]),(0,[z171,z203,z61,z4,z5,z6]),(0,[z961,z0,z1,z2,z4,z5]),(0,[z206,z859,z2,z4,z5,z6]),(0,[z0,z1,z19,z94,z2,z4])],[(0,[z59,z2,z336,z4,z5,z6]),(0,[z0,z1,z2,z4,z998,z6]),(0,[z0,z1,z2,z4,z5,z999]),(0,[z0,z1,z2,z4,z377,z96]),(0,[z108,z0,z2,z4,z5,z423])],[(0,[z0,z59,z740,z4,z5,z6]),(0,[z64,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1000]),(0,[z0,z1,z2,z4,z1001,z5])]],
   [[(0,[z59,z509,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z5,z232]),(0,[z0,z372,z2,z4,z5,z18]),(0,[z0,z1,z19,z141,z4,z5]),(0,[z0,z1,z21,z2,z763,z6])],[(0,[z480,z59,z2,z4,z79,z6]),(0,[z0,z59,z745,z2,z4,z5]),(0,[z76,z0,z318,z2,z4,z5]),(0,[z39,z134,z2,z41,z5,z6]),(0,[z1002,z0,z1,z2,z4,z5])],[(0,[z89,z1,z202,z2,z4,z5])],[(0,[z0,z14,z2,z4,z5,z20]),(0,[z59,z2,z4,z41,z5,z20]),(0,[z0,z59,z2,z4,z5,z115])],[(0,[z59,z2,z4,z515,z5,z6]),(0,[z0,z59,z54,z110,z5,z6])],[(0,[z633,z59,z145,z4,z5,z6]),(0,[z0,z59,z94,z2,z4,z6]),(0,[z116,z59,z2,z4,z5,z6]),(0,[z265,z1,z2,z4,z5,z6])],[],[(0,[z57,z59,z2,z4,z79,z6]),(0,[z306,z59,z2,z4,z5,z6]),(0,[z0,z1,z1003,z2,z4,z5]),(0,[z16,z0,z1,z95,z4,z5]),(0,[z0,z1,z2,z4,z1004,z6]),(0,[z0,z419,z2,z4,z5,z155])],[(0,[z59,z2,z4,z5,z6,z525]),(0,[z0,z1,z4,z5,z6,z1005])],[(0,[z0,z1,z2,z1006,z5,z6]),(0,[z1007,z203,z1,z2,z4,z5]),(0,[z171,z0,z61,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1008])],[(0,[z76,z166,z59,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1009]),(0,[z107,z2,z4,z79,z5,z6]),(0,[z0,z1,z511,z4,z126,z6])],[(0,[z175,z0,z2,z269,z5,z6]),(0,[z265,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z5,z763,z6])],[(0,[z71,z59,z31,z2,z4,z6]),(0,[z0,z1,z2,z4,z1010,z6])],[(0,[z0,z14,z2,z4,z297,z6]),(0,[z0,z1,z2,z4,z5,z1011])],[(0,[z0,z1012,z2,z4,z5,z6]),(0,[z0,z1,z31,z4,z196,z6]),(0,[z0,z911,z2,z4,z5,z18])],[]],
   [[(0,[z14,z490,z2,z4,z5,z6]),(0,[z417,z1,z2,z4,z5,z18]),(0,[z0,z2,z4,z5,z18,z1013])],[(0,[z287,z14,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1014]),(0,[z0,z1,z2,z4,z30,z6])],[(0,[z0,z123,z2,z4,z5,z20]),(0,[z0,z1015,z2,z4,z5,z6]),(0,[z0,z1016,z2,z4,z5,z6])],[(0,[z14,z502,z2,z4,z5,z6]),(0,[z307,z262,z2,z4,z5,z6]),(0,[z0,z1,z2,z371,z5,z18]),(0,[z0,z1017,z2,z4,z5,z6]),(0,[z0,z1018,z2,z4,z5,z6]),(0,[z629,z1,z2,z4,z5,z395])],[(0,[z398,z59,z2,z4,z5,z133]),(0,[z59,z2,z4,z555,z5,z6]),(0,[z0,z59,z2,z4,z5,z81]),(0,[z0,z59,z2,z4,z42,z6]),(0,[z134,z2,z4,z41,z5,z6]),(0,[z0,z1,z2,z4,z30,z232]),(0,[z0,z1,z2,z4,z20,z1019])],[(0,[z59,z2,z4,z389,z5,z6]),(0,[z0,z1,z2,z4,z5,z1020]),(0,[z1007,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z1021,z6]),(0,[z1022,z1,z2,z4,z5,z6]),(0,[z1023,z1,z2,z4,z5,z6]),(0,[z63,z64,z2,z4,z5,z216])],[(0,[z0,z1,z2,z4,z5,z18]),(0,[z0,z1024,z2,z4,z5,z6]),(0,[z0,z59,z52,z4,z5,z6]),(0,[z0,z1025,z2,z4,z5,z6]),(0,[z0,z1,z31,z4,z680,z6])],[(0,[z0,z59,z770,z2,z5,z6]),(0,[z72,z59,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z133,z760]),(0,[z0,z1,z2,z4,z30,z20])],[(0,[z0,z1,z1026,z2,z4,z5]),(0,[z0,z1,z4,z5,z20,z1027])],[(0,[z0,z1,z2,z4,z5,z1028])],[(0,[z338,z14,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z270]),(0,[z0,z1,z292,z4,z5,z341]),(0,[z0,z1,z2,z4,z1029,z6]),(0,[z0,z924,z2,z4,z5,z18])],[(0,[z1,z2,z4,z5,z6,z863])],[(0,[z0,z59,z2,z4,z5,z775]),(0,[z0,z1,z212,z2,z4,z18]),(0,[z0,z1,z1030,z2,z4,z6]),(0,[z307,z1,z2,z4,z42,z6]),(0,[z0,z1,z119,z121,z5,z6]),(0,[z0,z1,z2,z4,z5,z769])],[(0,[z59,z415,z2,z4,z5,z6]),(0,[z0,z1,z747,z2,z4,z6]),(0,[z0,z87,z2,z4,z5,z266]),(0,[z0,z1031,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1032]),(0,[z0,z1,z2,z4,z5,z1033]),(0,[z307,z1,z52,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1034])],[(0,[z0,z59,z202,z2,z4,z5]),(0,[z138,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1035]),(0,[z0,z256,z2,z122,z5,z577]),(0,[z0,z1,z4,z5,z18,z1036])]],
   [[(0,[z286,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1037,z6]),(0,[z1,z2,z4,z5,z832,z6])],[(0,[z0,z1,z1038,z2,z4,z5]),(0,[z1039,z1,z2,z4,z5,z6])],[(0,[z1002,z417,z1,z2,z4,z5])],[(0,[z0,z1,z2,z4,z6,z958])],[(1,[z59,z257,z2,z4,z6]),(0,[z0,z25,z2,z4,z5,z18]),(0,[z24,z1,z145,z4,z5,z18]),(0,[z71,z1,z2,z4,z135,z6]),(0,[z0,z2,z4,z143,z5,z18])],[(0,[z0,z14,z2,z4,z5,z797]),(0,[z0,z1,z2,z4,z5,z1040]),(0,[z976,z0,z1,z2,z4,z5]),(0,[z1041,z1,z2,z4,z5,z6]),(0,[z287,z1,z2,z4,z30,z6]),(0,[z0,z1,z2,z4,z5,z1042]),(0,[z0,z1,z4,z5,z755,z6])],[(0,[z290,z59,z2,z4,z79,z6]),(0,[z98,z1,z2,z4,z5,z250])],[(0,[z206,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1043]),(0,[z1044,z1,z2,z4,z5,z6])],[(0,[z1045,z0,z59,z2,z4,z5]),(0,[z76,z0,z2,z4,z5,z216]),(0,[z0,z1,z356,z4,z297,z6])],[(0,[z0,z1,z4,z1046,z5,z6]),(0,[z858,z1,z2,z4,z5,z18])],[(0,[z0,z1,z2,z4,z5,z1047])],[(0,[z16,z59,z2,z4,z5,z17]),(0,[z0,z1,z2,z4,z5,z1048])],[(0,[z0,z1,z11,z517,z35,z6])],[(0,[z206,z0,z2,z4,z5,z20]),(0,[z0,z1,z511,z4,z35,z6]),(0,[z0,z1049,z2,z4,z5,z6])],[(0,[z16,z265,z1,z2,z4,z5])],[(1,[z708,z2,z4,z5,z6]),(0,[z59,z2,z612,z4,z5,z6])]],
   [[(0,[z0,z1050,z2,z4,z5,z6]),(0,[z287,z286,z2,z4,z5,z6]),(0,[z0,z1,z2,z289,z5,z20]),(0,[z1,z2,z4,z5,z18,z1051])],[(0,[z16,z59,z2,z4,z5,z6]),(0,[z39,z1,z292,z41,z5,z6]),(0,[z0,z201,z318,z2,z4,z5]),(0,[z0,z99,z2,z4,z944,z6])],[(0,[z0,z245,z2,z4,z5,z6]),(0,[z0,z59,z2,z4,z5,z177])],[(0,[z414,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1052]),(0,[z63,z0,z318,z2,z4,z5])],[(0,[z0,z1,z1053,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1054]),(0,[z0,z1,z1055,z4,z5,z6])],[(0,[z0,z1,z257,z2,z4,z6]),(0,[z0,z1,z2,z4,z1056,z6]),(0,[z0,z1,z1057,z2,z4,z6]),(0,[z0,z1,z511,z4,z5,z18]),(0,[z0,z1,z8,z2,z4,z96])],[(0,[z510,z59,z2,z4,z5,z6]),(0,[z0,z220,z84,z4,z5,z6]),(0,[z1058,z0,z1,z2,z4,z5])],[],[(0,[z59,z2,z4,z5,z20,z133]),(0,[z0,z59,z2,z4,z5,z199]),(0,[z551,z59,z2,z4,z5,z6]),(0,[z0,z364,z2,z122,z5,z6]),(0,[z0,z14,z910,z4,z5,z6]),(0,[z0,z245,z2,z4,z5,z20]),(0,[z16,z1,z2,z4,z5,z760]),(0,[z203,z2,z122,z4,z5,z6]),(0,[z1059,z1,z2,z4,z5,z6]),(0,[z499,z1,z2,z4,z5,z250])],[(0,[z0,z1,z2,z711,z5,z6]),(0,[z0,z873,z2,z4,z5,z18])],[(0,[z59,z2,z4,z5,z133,z18]),(0,[z417,z14,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1060]),(0,[z0,z1,z2,z585,z5,z18]),(0,[z0,z1061,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1062,z5,z6]),(0,[z0,z1,z257,z2,z4,z20]),(0,[z98,z142,z2,z4,z5,z133])],[(0,[z59,z2,z4,z486,z5,z6]),(0,[z98,z1,z2,z4,z5,z706]),(0,[z0,z1,z2,z4,z5,z1063]),(0,[z0,z1,z2,z4,z6,z948])],[(0,[z154,z59,z2,z4,z5,z6])],[(0,[z16,z59,z2,z4,z5,z34]),(0,[z0,z59,z823,z4,z5,z6]),(0,[z0,z1,z2,z4,z782,z5])],[(0,[z1,z59,z257,z2,z4,z6]),(0,[z0,z14,z19,z4,z5,z65]),(0,[z0,z1,z2,z4,z6,z1064]),(0,[z265,z316,z2,z4,z5,z6]),(0,[z0,z1,z119,z66,z263,z6])]],
   [[(0,[z0,z14,z2,z4,z5,z6]),(0,[z59,z503,z2,z4,z5,z6]),(0,[z0,z1,z1065,z4,z5,z6]),(0,[z0,z1,z2,z4,z763,z6])],[(0,[z219,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1066,z6]),(0,[z0,z1,z202,z212,z2,z4]),(0,[z0,z1,z2,z4,z5,z1067]),(0,[z966,z1,z2,z4,z5,z18])],[(0,[z27,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1068,z6]),(0,[z0,z1,z8,z2,z4,z759])],[(0,[z251,z59,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z6,z86]),(0,[z0,z14,z2,z4,z5,z443]),(0,[z0,z1069,z2,z4,z5,z6])],[(0,[z0,z14,z2,z4,z922,z6]),(0,[z0,z1,z1070,z4,z5,z6]),(0,[z0,z1,z4,z5,z33,z726])],[(0,[z0,z1,z2,z4,z5,z1071]),(0,[z63,z0,z2,z4,z5,z738]),(0,[z0,z1,z4,z5,z6,z88])],[(0,[z0,z59,z2,z4,z5,z22]),(0,[z0,z14,z212,z2,z4,z6])],[(0,[z193,z1,z2,z4,z5,z6]),(0,[z16,z318,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z20,z211])],[(0,[z0,z1,z2,z4,z5,z1072]),(0,[z59,z2,z4,z5,z6,z250]),(0,[z1045,z0,z1,z2,z4,z5])],[(0,[z400,z59,z2,z4,z5,z18]),(0,[z251,z59,z2,z4,z5,z20]),(0,[z0,z437,z2,z4,z297,z6]),(0,[z0,z1073,z2,z4,z5,z6]),(0,[z171,z287,z2,z4,z5,z6]),(0,[z0,z1074,z2,z4,z5,z20]),(0,[z0,z1,z432,z4,z5,z305])],[(0,[z59,z2,z4,z520,z5,z6]),(0,[z787,z59,z2,z4,z5,z6]),(0,[z0,z59,z2,z4,z5,z232]),(0,[z0,z1075,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z714]),(0,[z0,z1,z21,z2,z126,z18])],[(0,[z0,z14,z31,z4,z239,z6]),(0,[z1076,z1,z2,z4,z5,z6])],[(0,[z0,z59,z2,z4,z5,z20]),(0,[z193,z1,z2,z4,z5,z20])],[(0,[z24,z14,z145,z4,z5,z6]),(0,[z0,z14,z935,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1077]),(0,[z0,z1,z2,z4,z5,z1078])],[(0,[z59,z2,z4,z671,z5,z6]),(0,[z59,z2,z4,z672,z5,z6]),(0,[z0,z123,z2,z4,z5,z6])]],
   [[(0,[z24,z1,z778,z4,z5,z6]),(0,[z0,z1,z53,z4,z42,z6])],[(0,[z400,z398,z59,z2,z4,z5]),(0,[z59,z2,z4,z675,z5,z6]),(0,[z0,z347,z2,z4,z5,z18]),(0,[z0,z1,z1079,z2,z4,z5]),(0,[z0,z1,z2,z4,z1080,z6]),(0,[z0,z1,z2,z4,z5,z1081]),(0,[z0,z1082,z2,z4,z5,z6])],[(0,[z0,z1083,z2,z4,z5,z6]),(0,[z89,z1,z2,z4,z5,z541]),(0,[z0,z1,z1084,z4,z5,z6]),(0,[z307,z1,z2,z4,z5,z232]),(0,[z1085,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z217,z18]),(0,[z0,z1,z48,z4,z392,z6])],[(0,[z105,z59,z2,z41,z5,z6]),(0,[z0,z1,z1086,z2,z4,z5])],[(0,[z0,z1087,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z328,z20]),(0,[z0,z1,z2,z4,z5,z44])],[(0,[z0,z14,z2,z4,z5,z321]),(0,[z307,z1,z2,z4,z5,z20])],[(0,[z14,z398,z59,z2,z4,z5]),(0,[z59,z684,z2,z4,z5,z6]),(0,[z0,z1,z1088,z4,z5,z6]),(0,[z1089,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1090,z6])],[(0,[z0,z59,z2,z4,z297,z6]),(0,[z0,z134,z292,z4,z5,z6]),(0,[z0,z2,z4,z944,z136,z6])],[(0,[z16,z1,z195,z2,z4,z5]),(0,[z0,z1,z2,z4,z90,z759])],[(0,[z146,z59,z2,z4,z5,z6])],[(0,[z63,z0,z2,z4,z5,z216]),(0,[z0,z1,z2,z4,z5,z281]),(0,[z0,z1,z2,z4,z5,z1091])],[(0,[z287,z59,z2,z4,z5,z6]),(0,[z0,z1,z356,z4,z5,z6]),(0,[z0,z1092,z2,z4,z5,z6])],[(0,[z98,z1,z391,z2,z4,z5]),(0,[z13,z307,z2,z269,z5,z6]),(0,[z417,z149,z2,z4,z5,z6])],[(0,[z59,z2,z4,z5,z702,z6]),(0,[z59,z2,z4,z5,z6,z704]),(0,[z24,z123,z145,z4,z5,z6]),(0,[z105,z1,z2,z711,z5,z6]),(0,[z105,z1,z2,z40,z5,z500]),(0,[z0,z1,z2,z4,z5,z1093])],[(0,[z59,z2,z4,z5,z6,z706]),(0,[z105,z1,z2,z40,z5,z77])],[(0,[z59,z2,z3,z4,z5,z6]),(0,[z59,z2,z4,z5,z7,z6]),(0,[z0,z14,z511,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1094]),(0,[z0,z1,z1095,z2,z4,z5]),(0,[z0,z1096,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z385,z199]),(0,[z0,z1,z19,z94,z4,z5]),(0,[z0,z1097,z2,z4,z5,z6])]],
   [[],[(0,[z59,z2,z4,z5,z23,z6]),(0,[z76,z105,z59,z2,z4,z5]),(0,[z0,z1,z356,z4,z5,z20])],[(0,[z0,z1,z2,z4,z42,z439]),(0,[z265,z1,z2,z4,z5,z18]),(0,[z0,z2,z4,z5,z216,z738]),(0,[z0,z1098,z2,z4,z5,z20]),(0,[z0,z1,z2,z345,z5,z20])],[(0,[z166,z1,z191,z4,z5,z6]),(0,[z0,z318,z2,z4,z5,z20]),(0,[z13,z0,z53,z269,z5,z6]),(0,[z0,z1,z2,z4,z1099,z6]),(0,[z0,z1,z2,z4,z1100,z6])],[(0,[z338,z59,z2,z4,z5,z6]),(0,[z0,z1,z52,z4,z5,z439]),(0,[z0,z1,z2,z4,z5,z187]),(0,[z0,z1,z1101,z2,z4,z20])],[(0,[z59,z2,z51,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1102]),(0,[z0,z1,z31,z4,z239,z18]),(0,[z1103,z1,z2,z4,z5,z6])],[(0,[z63,z0,z2,z4,z5,z23]),(0,[z171,z0,z61,z4,z5,z18]),(0,[z0,z1,z2,z4,z34,z698])],[(0,[z0,z1104,z2,z4,z5,z6]),(1,[z859,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z757]),(0,[z0,z14,z2,z4,z5,z541]),(0,[z0,z1,z94,z2,z4,z224]),(0,[z0,z1,z19,z94,z4,z65])],[(0,[z59,z70,z2,z4,z5,z6]),(0,[z166,z1,z191,z4,z5,z20]),(0,[z16,z466,z2,z4,z5,z17]),(0,[z0,z1,z4,z5,z6,z1036])],[(0,[z24,z1,z202,z145,z4,z5]),(0,[z0,z1,z1105,z2,z4,z5])],[(0,[z0,z1,z2,z4,z1106,z6]),(0,[z1107,z1,z2,z4,z5,z6]),(0,[z0,z1108,z2,z4,z5,z6])],[(0,[z0,z59,z2,z4,z877,z5]),(0,[z287,z256,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z726])],[],[(0,[z0,z1,z1109,z2,z4,z5]),(0,[z0,z1110,z2,z4,z5,z6]),(0,[z629,z1,z2,z4,z5,z133]),(0,[z0,z1,z119,z66,z5,z199]),(0,[z0,z1,z2,z5,z475,z18])],[(0,[z0,z398,z2,z4,z5,z277]),(0,[z0,z1,z4,z32,z755,z6]),(0,[z0,z1,z2,z552,z5,z18])]],
   [[(0,[z171,z0,z376,z4,z5,z6]),(0,[z166,z123,z2,z4,z5,z6])],[(0,[z0,z941,z2,z4,z5,z6]),(0,[z0,z568,z84,z4,z5,z6]),(0,[z1,z2,z4,z79,z832,z6])],[(0,[z0,z1111,z2,z4,z5,z6]),(0,[z0,z1,z4,z674,z32,z6])],[(0,[z400,z708,z2,z4,z5,z6]),(0,[z59,z2,z4,z79,z5,z115]),(0,[z0,z1,z2,z4,z1112,z5]),(0,[z0,z1,z2,z484,z5,z18])],[(0,[z0,z1,z2,z4,z5,z1113])],[(0,[z480,z0,z2,z4,z453,z6]),(0,[z0,z2,z4,z1114,z5,z6]),(0,[z0,z14,z21,z2,z126,z6]),(0,[z13,z0,z2,z269,z5,z439])],[(0,[z633,z0,z61,z4,z5,z6]),(0,[z0,z398,z2,z4,z5,z37]),(1,[z0,z2,z4,z5,z738])],[(0,[z1115,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z1116,z6]),(0,[z0,z1,z2,z121,z35,z6])],[(0,[z0,z934,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1117]),(0,[z14,z708,z2,z4,z5,z6])],[(0,[z0,z1,z511,z4,z5,z281])],[(0,[z0,z1,z237,z2,z5,z18]),(0,[z0,z1,z2,z5,z18,z272]),(0,[z0,z1,z174,z2,z4,z96])],[],[(0,[z0,z437,z2,z4,z5,z6]),(0,[z0,z59,z21,z2,z126,z6]),(0,[z138,z59,z2,z4,z5,z18]),(0,[z466,z59,z2,z4,z5,z6]),(0,[z105,z262,z2,z40,z5,z6])],[(0,[z1,z2,z4,z711,z5,z6]),(0,[z0,z1,z2,z4,z90,z34])],[(0,[z0,z1,z2,z4,z1118,z6])],[]],
   [[(0,[z332,z1,z145,z4,z5,z6]),(0,[z0,z1,z2,z4,z297,z341]),(0,[z0,z1,z237,z2,z5,z769])],[(0,[z0,z1,z2,z518,z5,z18]),(0,[z71,z1,z2,z4,z135,z18]),(0,[z0,z1,z275,z2,z4,z360])],[(0,[z0,z437,z2,z4,z5,z20]),(0,[z0,z1,z4,z5,z6,z1027])],[(0,[z76,z0,z201,z2,z4,z5]),(0,[z203,z2,z61,z4,z5,z6]),(0,[z0,z1,z54,z831,z5,z6])],[(0,[z417,z59,z2,z4,z5,z6]),(0,[z1119,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1118,z20])],[(0,[z0,z466,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z998,z6]),(0,[z0,z1,z2,z4,z755,z6])],[(0,[z0,z1074,z2,z4,z5,z6]),(0,[z0,z1,z53,z4,z5,z232]),(0,[z0,z201,z2,z4,z5,z738]),(0,[z0,z1,z94,z4,z33,z6])],[(0,[z0,z1,z2,z4,z5,z1120]),(0,[z0,z1,z1121,z4,z5,z6]),(0,[z0,z1122,z2,z4,z5,z6])],[(0,[z0,z1123,z2,z4,z5,z6])],[(0,[z0,z59,z19,z4,z5,z65]),(0,[z0,z1,z53,z4,z5,z20]),(0,[z0,z1,z21,z2,z126,z44])],[(0,[z0,z59,z2,z4,z5,z6]),(0,[z0,z1,z31,z68,z4,z239])],[(0,[z0,z1,z1124,z4,z5,z6]),(0,[z0,z201,z2,z4,z5,z296]),(0,[z0,z466,z2,z4,z5,z20]),(0,[z0,z1,z1125,z4,z5,z6]),(0,[z859,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z1126,z5,z6]),(0,[z0,z1,z2,z5,z769,z18])],[(0,[z71,z59,z2,z4,z79,z6]),(0,[z0,z1,z2,z4,z5,z801]),(0,[z265,z14,z2,z4,z5,z6]),(0,[z98,z0,z1,z95,z4,z5]),(0,[z0,z1,z2,z4,z5,z67]),(0,[z0,z1,z31,z68,z2,z4])],[(0,[z0,z59,z2,z4,z6,z86]),(0,[z0,z59,z2,z4,z5,z443]),(0,[z0,z2,z4,z100,z944,z6]),(0,[z739,z1,z2,z4,z5,z6]),(0,[z0,z1,z94,z9,z2,z4])],[(0,[z16,z59,z2,z4,z5,z18])],[(0,[z708,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1127]),(0,[z1128,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1129]),(0,[z0,z1,z2,z334,z126,z6])]],
   [[(0,[z0,z59,z212,z2,z4,z6]),(0,[z0,z220,z388,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1130])],[(0,[z14,z59,z2,z4,z5,z18]),(0,[z59,z202,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z328,z6]),(0,[z57,z442,z2,z4,z79,z6]),(0,[z0,z1,z2,z4,z5,z760]),(0,[z0,z1,z2,z803,z5,z6]),(0,[z0,z1131,z2,z4,z5,z6]),(0,[z0,z1,z1132,z4,z5,z6])],[(0,[z307,z1,z2,z4,z5,z6]),(0,[z76,z0,z59,z2,z4,z5]),(0,[z0,z1,z808,z4,z5,z6]),(0,[z0,z1,z1133,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1134]),(0,[z0,z1,z95,z4,z5,z65])],[(0,[z0,z1135,z2,z4,z5,z6]),(0,[z0,z220,z84,z4,z5,z18]),(1,[z0,z1,z831,z5,z6])],[(0,[z0,z1136,z2,z4,z5,z6])],[(0,[z0,z1137,z2,z4,z5,z6]),(0,[z105,z106,z2,z40,z5,z6]),(0,[z0,z1138,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1139,z6]),(0,[z16,z398,z59,z2,z4,z5]),(0,[z0,z59,z31,z4,z239,z6]),(0,[z0,z1,z814,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z725]),(0,[z39,z1,z2,z41,z297,z6]),(0,[z0,z47,z84,z4,z5,z6]),(0,[z287,z1,z53,z4,z5,z6]),(0,[z0,z1,z1140,z2,z4,z5])],[(0,[z24,z59,z145,z4,z5,z6]),(0,[z0,z1,z1141,z2,z4,z6])],[],[(0,[z0,z1,z594,z110,z5,z6]),(0,[z0,z1,z1142,z2,z4,z5])],[(0,[z175,z1,z2,z41,z5,z6]),(0,[z0,z1,z2,z4,z822,z5]),(0,[z0,z1,z2,z4,z5,z1143]),(0,[z0,z1144,z2,z4,z5,z6]),(0,[z0,z1,z432,z4,z5,z33])],[(0,[z0,z59,z2,z4,z938,z6]),(0,[z285,z59,z2,z4,z5,z6]),(0,[z649,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1145,z6]),(0,[z0,z1,z19,z94,z4,z6])],[(0,[z0,z14,z2,z4,z5,z18]),(0,[z59,z2,z4,z41,z5,z18]),(0,[z0,z1,z2,z4,z5,z815]),(0,[z0,z2,z4,z5,z6,z1013])],[(0,[z59,z2,z4,z5,z250,z18]),(0,[z1146,z0,z2,z4,z5,z6]),(0,[z0,z1,z778,z4,z5,z6]),(0,[z1147,z1,z2,z4,z5,z6]),(0,[z0,z256,z2,z122,z5,z6]),(0,[z0,z2,z4,z944,z5,z6]),(0,[z0,z1,z2,z4,z5,z12])],[(0,[z0,z59,z2,z4,z5,z321]),(0,[z0,z1,z2,z4,z1148,z6]),(0,[z0,z1,z1149,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1150]),(0,[z0,z1098,z2,z4,z5,z6])]],
   [[(0,[z0,z318,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1151])],[(0,[z687,z59,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z5,z270]),(0,[z0,z1,z2,z4,z5,z1152]),(0,[z0,z1,z1101,z2,z4,z6])],[(0,[z0,z1,z68,z48,z2,z4])],[(0,[z0,z1,z2,z4,z263,z199])],[(0,[z71,z934,z2,z4,z5,z6]),(0,[z0,z59,z949,z2,z5,z6]),(0,[z0,z1,z833,z2,z5,z6]),(0,[z0,z1,z2,z1153,z5,z6]),(0,[z0,z256,z2,z122,z5,z20])],[(0,[z0,z1,z1154,z4,z5,z6])],[(0,[z394,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1155])],[(0,[z0,z1,z2,z4,z5,z741])],[(0,[z0,z72,z2,z4,z5,z20]),(0,[z0,z1156,z2,z4,z5,z6])],[(0,[z0,z59,z511,z4,z5,z6]),(0,[z0,z1,z1157,z2,z4,z5]),(0,[z287,z1,z2,z4,z5,z439]),(0,[z0,z1158,z2,z4,z5,z6])],[],[(0,[z166,z59,z2,z4,z5,z6]),(0,[z0,z59,z2,z4,z5,z870]),(0,[z71,z14,z2,z4,z135,z6])],[(0,[z59,z2,z4,z291,z5,z6]),(0,[z16,z201,z59,z2,z4,z5]),(0,[z0,z123,z2,z4,z5,z18]),(0,[z0,z1,z1159,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1160]),(0,[z0,z99,z2,z4,z136,z6]),(0,[z0,z2,z4,z1161,z5,z6]),(0,[z0,z1,z444,z2,z5,z18]),(0,[z0,z1,z95,z8,z2,z4])],[(0,[z0,z1,z2,z1162,z5,z6])],[(0,[z105,z59,z2,z4,z5,z6])],[(0,[z171,z0,z779,z4,z5,z6]),(0,[z0,z2,z4,z5,z18,z762])]],
   [[(0,[z0,z59,z965,z2,z4,z6]),(0,[z0,z1,z933,z2,z4,z5]),(0,[z1163,z1,z2,z4,z5,z6])],[(0,[z89,z14,z2,z4,z5,z6]),(0,[z166,z59,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z30,z18]),(0,[z0,z1,z2,z4,z385,z6]),(0,[z0,z1,z2,z4,z5,z1164])],[(0,[z0,z59,z2,z4,z5,z541]),(0,[z76,z0,z1,z2,z4,z5]),(0,[z0,z1,z312,z2,z4,z5]),(0,[z0,z1165,z2,z4,z5,z6]),(0,[z0,z99,z2,z4,z136,z20]),(0,[z0,z1,z48,z4,z755,z6])],[(0,[z0,z1,z2,z4,z5,z341]),(0,[z0,z134,z2,z4,z5,z20]),(0,[z98,z265,z1,z2,z4,z5])],[(0,[z105,z59,z2,z4,z5,z20]),(0,[z0,z576,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z944,z6])],[],[(0,[z71,z59,z2,z4,z5,z6]),(0,[z57,z1,z684,z2,z4,z6]),(0,[z0,z1,z19,z458,z4,z5])],[(0,[z89,z14,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z5,z1166]),(0,[z0,z1,z2,z4,z385,z20]),(0,[z0,z1,z2,z4,z5,z1167])],[(0,[z0,z1,z2,z4,z5,z1168]),(0,[z13,z203,z2,z4,z5,z6])],[(0,[z0,z149,z2,z4,z104,z6]),(0,[z0,z2,z4,z1169,z5,z6])],[(0,[z0,z576,z2,z4,z5,z20]),(0,[z0,z1,z2,z334,z5,z18])],[(0,[z0,z1,z2,z4,z1170,z6]),(0,[z0,z59,z971,z2,z4,z6]),(0,[z0,z59,z2,z4,z5,z972]),(0,[z0,z1,z4,z517,z5,z20]),(0,[z0,z1,z1171,z4,z5,z20])],[(0,[z71,z59,z2,z4,z5,z20]),(0,[z694,z59,z2,z4,z5,z6]),(0,[z0,z14,z8,z2,z4,z96]),(0,[z0,z1,z356,z4,z5,z270]),(0,[z0,z1,z1172,z4,z5,z6]),(0,[z16,z1,z2,z4,z5,z488])],[(0,[z300,z59,z2,z4,z5,z6]),(0,[z59,z2,z4,z79,z5,z20]),(0,[z0,z134,z2,z4,z297,z6]),(0,[z98,z1,z2,z4,z5,z760]),(0,[z0,z84,z4,z622,z5,z6]),(0,[z1,z2,z4,z5,z6,z1051]),(0,[z0,z1,z511,z4,z5,z12]),(0,[z0,z1031,z2,z4,z5,z18]),(0,[z0,z1,z446,z4,z5,z43])],[(0,[z105,z1,z2,z40,z5,z20]),(0,[z0,z1,z2,z4,z5,z1173])],[(0,[z76,z0,z14,z2,z4,z5]),(0,[z338,z72,z2,z4,z5,z6]),(0,[z0,z1,z570,z110,z5,z6])]],
   [[(0,[z184,z59,z2,z4,z5,z6]),(0,[z0,z1,z119,z66,z5,z6]),(0,[z0,z1174,z2,z4,z5,z6]),(0,[z0,z805,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z6,z1019]),(0,[z0,z1,z2,z4,z5,z1175])],[(0,[z71,z1,z2,z4,z650,z6]),(0,[z0,z1176,z2,z4,z5,z6])],[(0,[z59,z119,z145,z4,z5,z6]),(0,[z0,z1,z257,z4,z110,z6]),(0,[z98,z1,z2,z4,z5,z133]),(0,[z0,z1,z2,z4,z1177,z6]),(0,[z0,z1178,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1179,z5,z6]),(0,[z0,z1,z1180,z4,z5,z6]),(0,[z0,z1,z1181,z2,z4,z5])],[(0,[z405,z59,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z33,z224]),(0,[z0,z1,z2,z4,z5,z1182])],[(0,[z0,z59,z2,z4,z5,z989]),(0,[z0,z1,z1183,z4,z5,z6]),(0,[z0,z1,z53,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1184]),(0,[z0,z1,z119,z66,z5,z20]),(0,[z0,z1,z2,z4,z5,z1185]),(0,[z0,z1,z95,z4,z5,z6])],[(0,[z0,z290,z2,z4,z234,z6]),(0,[z206,z0,z2,z4,z5,z18]),(0,[z0,z1,z9,z4,z5,z33])],[(0,[z0,z737,z2,z4,z5,z6]),(0,[z1,z191,z778,z4,z5,z6])],[(0,[z59,z2,z4,z5,z168,z6]),(0,[z0,z1,z2,z4,z5,z876]),(0,[z0,z2,z4,z1186,z5,z6])],[(0,[z39,z1,z2,z41,z5,z6])],[(0,[z204,z0,z2,z4,z80,z6]),(0,[z0,z1,z2,z4,z5,z1187]),(0,[z0,z1,z2,z198,z35,z6]),(0,[z0,z1,z2,z4,z5,z1188]),(0,[z0,z1,z2,z4,z90,z571])],[(0,[z0,z14,z4,z5,z6,z88]),(0,[z0,z1,z2,z4,z1189,z20]),(0,[z0,z1,z95,z4,z5,z20])],[(0,[z0,z1190,z2,z4,z5,z6]),(0,[z1191,z1,z2,z4,z5,z6]),(0,[z206,z0,z84,z4,z5,z6]),(0,[z0,z1,z2,z11,z35,z20])],[(0,[z59,z2,z376,z4,z5,z6]),(0,[z0,z779,z61,z4,z5,z6]),(0,[z0,z1,z2,z681,z5,z18])],[(0,[z0,z1,z52,z4,z42,z6]),(0,[z0,z201,z2,z4,z5,z37]),(0,[z0,z1,z31,z4,z533,z6])]],
   [[(0,[z39,z1,z2,z41,z5,z20]),(0,[z0,z1,z2,z4,z5,z1192])],[(0,[z59,z2,z4,z194,z5,z6]),(0,[z0,z1,z2,z4,z5,z789]),(0,[z1193,z1,z2,z4,z5,z6])],[(0,[z59,z2,z4,z387,z5,z6]),(0,[z0,z245,z2,z4,z5,z18]),(0,[z0,z201,z2,z4,z5,z155]),(0,[z0,z1194,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1195]),(0,[z0,z1,z48,z4,z32,z6])],[(0,[z0,z1,z2,z4,z5,z1196]),(0,[z0,z1,z2,z4,z310,z315])],[(0,[z0,z1,z257,z2,z4,z18]),(0,[z0,z1197,z2,z4,z5,z6])],[(0,[z265,z59,z2,z4,z5,z6]),(0,[z0,z1198,z1,z2,z4,z5]),(0,[z0,z1,z9,z4,z5,z726])],[(0,[z59,z212,z2,z145,z4,z6]),(0,[z492,z14,z2,z4,z5,z6]),(0,[z0,z442,z2,z4,z5,z20]),(0,[z0,z1,z19,z4,z390,z5])],[(0,[z105,z941,z2,z4,z5,z6]),(1,[z0,z779,z4,z5,z6]),(0,[z0,z84,z52,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z439])],[(0,[z59,z2,z4,z5,z395,z20]),(0,[z0,z1,z48,z4,z32,z20]),(0,[z0,z1,z754,z4,z5,z6])],[(0,[z0,z59,z2,z1006,z5,z6]),(0,[z0,z1199,z2,z4,z5,z6])],[(0,[z0,z14,z2,z4,z30,z6]),(0,[z24,z1,z212,z145,z4,z6]),(0,[z1200,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1201]),(0,[z0,z1,z95,z4,z34,z6])],[(0,[z59,z2,z4,z230,z5,z6]),(0,[z677,z59,z2,z4,z5,z6]),(0,[z480,z0,z2,z4,z100,z6]),(0,[z0,z1,z2,z4,z1202,z6]),(0,[z0,z1203,z2,z4,z5,z6])],[(0,[z0,z59,z2,z4,z1010,z6]),(0,[z0,z1,z2,z4,z1204,z5])],[(0,[z0,z1,z2,z4,z5,z1205]),(0,[z0,z1,z2,z4,z5,z1206]),(0,[z0,z1,z2,z4,z5,z1207])],[(0,[z0,z1,z2,z908,z4,z6]),(0,[z0,z1,z2,z4,z1208,z6]),(0,[z0,z87,z2,z4,z5,z37]),(0,[z0,z1209,z2,z4,z5,z6])]],
   [[(0,[z13,z0,z2,z269,z42,z6]),(0,[z0,z1210,z2,z4,z5,z6])],[(0,[z59,z2,z4,z5,z6,z249]),(0,[z0,z14,z2,z4,z5,z281]),(0,[z166,z347,z191,z4,z5,z6])],[(0,[z0,z14,z356,z4,z5,z6]),(0,[z13,z0,z52,z269,z5,z6]),(0,[z0,z1,z19,z4,z5,z726])],[(0,[z0,z14,z398,z2,z4,z5]),(0,[z0,z1,z292,z4,z5,z20]),(0,[z0,z1069,z2,z4,z5,z18])],[(0,[z59,z2,z4,z5,z445,z6]),(0,[z0,z1211,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1212,z6]),(0,[z0,z256,z2,z122,z5,z443])],[(0,[z0,z72,z2,z4,z5,z6]),(0,[z0,z1,z1213,z2,z4,z5]),(0,[z0,z1,z2,z596,z5,z18])],[(0,[z89,z245,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z5,z1094]),(0,[z0,z2,z4,z5,z1214,z6]),(0,[z0,z1,z4,z5,z726,z65])],[(0,[z0,z59,z2,z4,z5,z18]),(0,[z59,z202,z2,z145,z4,z5]),(0,[z193,z1,z2,z4,z5,z18]),(0,[z242,z0,z2,z4,z944,z6]),(0,[z0,z1,z2,z4,z5,z1215])],[],[(0,[z89,z1,z257,z2,z4,z6]),(0,[z0,z1216,z2,z4,z5,z6])],[(0,[z0,z59,z2,z4,z5,z1028]),(0,[z0,z1,z1217,z2,z4,z5]),(0,[z63,z265,z2,z4,z5,z216]),(0,[z0,z1218,z2,z4,z5,z6])],[(0,[z0,z59,z2,z4,z5,z270]),(0,[z0,z14,z2,z4,z5,z187]),(0,[z0,z1,z2,z4,z1219,z6]),(0,[z0,z1,z1220,z4,z5,z6]),(0,[z1221,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1222]),(1,[z1,z2,z4,z832,z6]),(0,[z1223,z1,z2,z4,z5,z6]),(0,[z1128,z1,z2,z4,z5,z18]),(0,[z0,z2,z4,z5,z1214,z20])],[(0,[z0,z1,z2,z4,z5,z1224]),(0,[z0,z1,z292,z4,z297,z6]),(0,[z417,z99,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z224]),(0,[z0,z1,z31,z458,z4,z6])],[(0,[z0,z1,z4,z927,z5,z6]),(0,[z0,z1,z2,z4,z328,z18]),(0,[z0,z1,z119,z4,z385,z6]),(0,[z0,z1,z31,z68,z4,z5]),(0,[z0,z1,z2,z368,z5,z20]),(0,[z138,z1,z2,z4,z5,z45])],[(0,[z0,z398,z59,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z918]),(0,[z307,z1,z2,z4,z5,z18])]],
   [[(0,[z0,z134,z2,z4,z5,z6]),(0,[z0,z286,z2,z160,z5,z6]),(0,[z0,z1,z2,z4,z5,z1225]),(0,[z1226,z1,z2,z4,z5,z6])],[(0,[z242,z0,z2,z4,z80,z6]),(0,[z0,z1,z2,z4,z5,z1227]),(0,[z0,z1,z1228,z2,z4,z6]),(0,[z1229,z1,z2,z4,z5,z6]),(0,[z64,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z5,z1230])],[(0,[z0,z59,z1038,z2,z4,z5]),(0,[z0,z14,z2,z4,z1106,z6]),(0,[z0,z1,z2,z4,z328,z270]),(0,[z57,z1,z2,z4,z79,z115])],[(0,[z1231,z0,z2,z4,z5,z6]),(0,[z859,z2,z4,z110,z5,z6])],[(0,[z0,z1,z1232,z4,z5,z6])],[(0,[z71,z59,z2,z4,z135,z6]),(0,[z0,z1233,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z263,z6]),(0,[z0,z1,z31,z4,z755,z6]),(1,[z0,z1,z2,z763,z6])],[(0,[z59,z2,z4,z60,z5,z6]),(0,[z0,z1234,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z577])],[(0,[z560,z59,z2,z4,z5,z6]),(0,[z0,z1,z4,z517,z5,z6]),(0,[z0,z1,z1171,z4,z5,z6])],[(0,[z0,z1,z31,z4,z239,z224])],[(0,[z59,z2,z4,z79,z5,z6]),(0,[z59,z2,z4,z80,z5,z6])],[(0,[z105,z1,z2,z40,z5,z6]),(0,[z0,z1,z356,z4,z5,z18]),(0,[z0,z1,z2,z4,z263,z20])],[(0,[z59,z2,z4,z5,z496,z6]),(0,[z0,z1,z2,z4,z5,z1235])],[(0,[z59,z2,z4,z498,z5,z6]),(0,[z0,z318,z2,z4,z5,z18]),(0,[z203,z220,z2,z4,z5,z6]),(0,[z0,z1236,z2,z4,z5,z6]),(0,[z0,z1,z68,z2,z4,z5]),(0,[z0,z1237,z2,z4,z5,z6])],[(0,[z0,z1,z2,z5,z534,z18])],[(0,[z236,z59,z2,z4,z5,z6]),(0,[z0,z14,z257,z2,z4,z6]),(0,[z0,z1,z2,z4,z6,z759])]],
   [[(0,[z166,z1,z614,z4,z5,z6]),(0,[z0,z1,z54,z110,z5,z81]),(0,[z0,z1,z31,z4,z637,z6])],[(0,[z59,z257,z2,z4,z5,z6]),(0,[z59,z2,z512,z4,z5,z6]),(0,[z0,z14,z237,z2,z5,z18]),(0,[z0,z1,z1238,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1239,z6]),(0,[z166,z1,z778,z4,z5,z6]),(0,[z0,z2,z122,z557,z5,z6]),(0,[z0,z1,z2,z4,z34,z224]),(0,[z0,z1,z129,z2,z5,z18])],[(0,[z193,z245,z2,z4,z5,z6]),(0,[z0,z1240,z2,z4,z5,z6]),(0,[z166,z1,z191,z4,z5,z18]),(0,[z0,z1,z2,z4,z42,z232])],[(0,[z0,z14,z2,z4,z90,z34]),(0,[z0,z1241,z2,z4,z5,z6])],[(0,[z0,z59,z1053,z4,z5,z6]),(0,[z0,z1,z52,z4,z5,z232]),(0,[z0,z1,z4,z1242,z5,z6])],[(0,[z0,z59,z2,z981,z4,z5]),(0,[z0,z59,z8,z2,z4,z96]),(0,[z0,z1,z2,z4,z42,z20]),(0,[z0,z1,z2,z4,z562,z112])],[(0,[z0,z730,z59,z2,z4,z5]),(0,[z0,z1,z2,z4,z1243,z6]),(0,[z1244,z0,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z864,z6]),(0,[z0,z1,z52,z4,z5,z20])],[(0,[z0,z1,z2,z4,z1189,z6])],[(0,[z0,z1,z2,z11,z35,z6])],[],[(0,[z59,z366,z2,z4,z5,z6]),(0,[z57,z107,z2,z4,z79,z6]),(0,[z242,z417,z2,z4,z100,z6]),(0,[z265,z2,z4,z5,z216,z6])],[(0,[z0,z1245,z2,z4,z5,z6]),(0,[z0,z1,z2,z664,z35,z6]),(0,[z318,z2,z4,z5,z133,z6]),(0,[z1244,z0,z2,z4,z5,z20])],[(0,[z0,z1246,z2,z4,z5,z6]),(0,[z0,z1,z9,z293,z4,z5]),(0,[z1247,z1,z2,z4,z5,z6])],[(0,[z59,z2,z4,z5,z541,z6]),(0,[z16,z59,z2,z4,z5,z133]),(0,[z0,z398,z1,z2,z4,z5]),(0,[z76,z1,z2,z4,z5,z133]),(0,[z0,z1,z2,z4,z1248,z6]),(0,[z0,z1249,z2,z4,z5,z6]),(0,[z0,z107,z2,z4,z5,z20]),(0,[z0,z1,z2,z1250,z5,z6]),(0,[z0,z1,z2,z4,z1251,z6]),(0,[z0,z1,z2,z5,z20,z695]),(0,[z1252,z1,z2,z4,z5,z6]),(0,[z0,z1,z94,z2,z4,z96])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 505) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 505).take 506) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1011).take 384) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1395)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [505, 506, 384] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 139).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 139).take 144).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 283).take 152).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 435).take 77).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [139, 144, 152, 77] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_38935

theorem PEqualNP.Outside.L_meta_38935 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4276150496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4276150496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38935.solve