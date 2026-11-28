import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38049

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
  Nat.testBit (4278124200 * 2 ^ 32 + 4274845832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x4040c066c1c862a2#64 ++ 0x2a020603360e4315#64 ++ 0xa141c0ffc3c867fb#64 ++ 0xfd0a0e07fe1e433f#64 : BitVec 256),
   (0x808223110413854c#64 ++ 0x0404111888209c2a#64 ++ 0x728627118c7f87ff#64 ++ 0x7b9431388c63fc3f#64 : BitVec 256),
   (0x00d8281a5070a988#64 ++ 0x4806c140d283854c#64 ++ 0xecf8381e7071f996#64 ++ 0xd767c1c0f3838fcc#64 : BitVec 256),
   (0x070015a02e815610#64 ++ 0x903800ad01740ab0#64 ++ 0xef003fe07f81fe1f#64 ++ 0xcf7801ff03fc0ff0#64 : BitVec 256),
   (0x076d40007b6c0000#64 ++ 0xe03b6a0003db6000#64 ++ 0xf7ffc0007ffe000e#64 ++ 0x3fbffe0003fff000#64 : BitVec 256),
   (0x0fb7bedd8000001f#64 ++ 0x007dbdf6ec000000#64 ++ 0xffffffff80000001#64 ++ 0xfffffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [2, 5]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [11, 7]⟩, ⟨.or, [1, 13]⟩, ⟨.and, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xecf8381e7071f996 0xd767c1c0f3838fcc

def z1 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xef003fe07f81fe1f 0xcf7801ff03fc0ff0

def z2 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xf7ffc0007ffe000e 0x3fbffe0003fff000

def z3 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffff80000001 0xfffffffffc000000

def z4 : W := mkw 0x4000402001884220 0x22000201000c4211 0x0000000003880668 0x00000000001c4033

def z5 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xa141c0ffc3c867fb 0xfd0a0e07fe1e433f

def z6 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x728627118c7f87ff 0x7b9431388c63fc3f

def z7 : W := mkw 0x40008046800020a2 0x0a00040234000105 0x0000001f800001e0 0x00000000fc00000f

def z8 : W := mkw 0x070014802a001010 0x903800a401500080 0x0c00180030001800 0x006000c0018000c0

def z9 : W := mkw 0x070014802a000010 0x803800a401500000 0xef003fe07f80000f 0xcf7801ff03fc0000

def z10 : W := mkw 0x000001202e815600 0x9000000901740ab0 0x620027007f81fe1f 0x4b10013803fc0ff0

def z11 : W := mkw 0x004800025070a980 0x480240001283854c 0x000000007071f996 0x0000000003838fcc

def z12 : W := mkw 0x0090281800000008 0x00048140c0000000 0xecf8381e00000000 0xd767c1c0f0000000

def z13 : W := mkw 0x070014a02a805210 0x903800a501540290 0xed0038e07381f816 0xc76801c7039c0fc0

def z14 : W := mkw 0x0f92bedd8000001f 0x007c95f6ec000000 0xef003fff80000001 0xcf7801fffc000000

def z15 : W := mkw 0x072d15a03ea55610 0xd03968ad01f52ab0 0xffbe3fe07fb7fe1f 0xcffdf1ff03fdbff0

def z16 : W := mkw 0x0725000000000000 0x0039280000000000 0xf7ffc00000000000 0x3fbffe0000000000

def z17 : W := mkw 0x0ffffeddfb6c001f 0xe07ffff6efdb6000 0xfffffffffffe000f 0xfffffffffffff000

def z18 : W := mkw 0x4f27d6e581884237 0x22793eb72c0c4211 0x1307c7e183880669 0x28983e3f0c1c4033

def z19 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0x0800381e7071f996 0xc04001c0f3838fcc

def z20 : W := mkw 0x00d8681a5178a988 0x6806c340d28bc54c 0xedf9f81e73f9f99e 0xff6fcfc0f39fcfcc

def z21 : W := mkw 0x0fb7bffd8481561f 0x107dbdffec240ab0 0xffffffff8001fe11 0xfffffffffc000ff0

def z22 : W := mkw 0x078236910000001c 0x003c11b488000000 0xff863ff180000001 0xfffc31ff8c000000

def z23 : W := mkw 0x476dc066fbec62a2 0xea3b6e0337df6315 0xf7ffc0fffffe67ff 0xffbffe07fffff33f

def z24 : W := mkw 0xc0c2e377c5dbe7ee 0x2e06171bbe2edf3f 0xf3c7e7ffcfffe7ff 0xff9e3f3ffe7fff3f

def z25 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0x8c78381e7001f990 0xc463c1c0f3800fcc

def z26 : W := mkw 0x07903db82e815618 0x903c81edc1740ab0 0xeff83ffe7f81fe1f 0xdf7fc1fff3fc0ff0

def z27 : W := mkw 0x8082a3558413854e 0x0404151aac209c2a 0xf3c7e7ff8c7f87ff 0xff9e3f3ffc63fc3f

def z28 : W := mkw 0x070014a02a805210 0x903800a501540290 0x010000e003800000 0x00080007001c0000

def z29 : W := mkw 0x4700d5e4af895632 0xb23806af257c4ab1 0xef01ffe1ff89fe7f 0xef780fff0ffc4ff3

def z30 : W := mkw 0x004840007b6c0000 0xe002420003db6000 0x000000007ffe000e 0x0000000003fff000

def z31 : W := mkw 0x076d55a07fed5610 0xf03b6aad03ff6ab0 0xffffffe07ffffe1f 0xffffffff03fffff0

def z32 : W := mkw 0x48f7ea7fc1c862af 0x2a47bf53fe0e4315 0xb1ffc0ffc3c867fb 0xfd8ffe07fe1e433f

def z33 : W := mkw 0x0040400041480000 0x20020200020a4000 0xa141c00043c8000a 0x3d0a0e00021e4000

def z34 : W := mkw 0x0098281a1030a988 0x4804c140d081854c 0x4cb8381e3031f994 0xc265c1c0f1818fcc

def z35 : W := mkw 0x0000000000000000 0x0000000000000000 0x728600000c7e000e 0x3b9430000063f000

def z36 : W := mkw 0x004801227ef1ff80 0xd802400913f78ffc 0x000000007ff1ff9e 0x0000000003ff8ffc

def z37 : W := mkw 0x4740d5e6efc976b2 0xba3a06af377e4bb5 0xef41ffee7f81fe1f 0xcf7a0fff73fc0ff0

def z38 : W := mkw 0x0000804480000002 0x0000040224000000 0x0101c0e180000001 0x28080e070c000000

def z39 : W := mkw 0x0fb7bedd8010811f 0x007dbdf6ec008408 0xffffffff80718197 0xfffffffffc038c0c

def z40 : W := mkw 0x878237910413855c 0x043c11bc88209c2a 0xff863ff18c7f87ff 0xfffc31ff8c63fc3f

def z41 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x20002711804987fb 0x790001388c024c3f

def z42 : W := mkw 0x80ef6211517e814c 0x64077b108a8bf40a 0x10ffc011807e01e0 0x3087fe008c03f00f

def z43 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0x0141c0ff83c807e9 0x380a0e07fc1e403f

def z44 : W := mkw 0x0058080a50602880 0x4802c04052830144 0x8c78180e70007800 0x8463c0c0738003c0

def z45 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0x030007e00f800609 0x0818003f007c0030

def z46 : W := mkw 0x0090281a0010a988 0x08048140d000854c 0x0800381e0001f990 0xc04001c0f0000fcc

def z47 : W := mkw 0x072540002b0c0000 0xa0392a0001586000 0x1307c0000f8e0008 0x28983e00007c7000

def z48 : W := mkw 0x000040002b0c0000 0xa000020001586000 0x000000000f8e0008 0x00000000007c7000

def z49 : W := mkw 0x40d8e85ed178a9aa 0x6a06c742f68bc54d 0x00f9c01f807801e0 0x3007ce00fc03c00f

def z50 : W := mkw 0x0fb7bffdae81561f 0x907dbdffed740ab0 0xffffffffff81fe1f 0xfffffffffffc0ff0

def z51 : W := mkw 0x006d40007b6c0000 0xe0036a0003db6000 0x10ffc0007ffe000e 0x3087fe0003fff000

def z52 : W := mkw 0x0700148000000010 0x003800a400000000 0xef003fe000000001 0xcf7801ff00000000

def z53 : W := mkw 0x07d83d9a7e71bd98 0xd83ec1ecd3f38dec 0xeef83f1e7c71f996 0xd777c1f8f3e38fcc

def z54 : W := mkw 0x0725000000000000 0x0039280000000000 0x56be000000000000 0x02b5f00000000000

def z55 : W := mkw 0x0000000000000000 0x0000000000000000 0xec0038007001f816 0xc76001c003800fc0

def z56 : W := mkw 0x0048000050600000 0x4002400002830000 0x00f8000000700000 0x1007c00000038000

def z57 : W := mkw 0x0040000240402080 0x0802000012020104 0xa040001e40406192 0xd5020000f202030c

def z58 : W := mkw 0x072d40003b2c0000 0xe0396a0001d96000 0x57bfc0003fbe000c 0x2abdfe0001fdf000

def z59 : W := mkw 0x000015a004815610 0x100000ad00240ab0 0x08003fe00001fe11 0xc04001ff00000ff0

def z60 : W := mkw 0x006d4000516c0000 0x60036a00028b6000 0x10ffc000007e0000 0x3087fe000003f000

def z61 : W := mkw 0x470095e6ae8176b2 0x9a3804af35740bb5 0xef003fffff81ffff 0xcf7801fffffc0fff

def z62 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xfffffffff001f817 0xffffffffff800fc0

def z63 : W := mkw 0x87ff6b1b7f7fadcc 0xec3ffb58dbfbfd6e 0xffffff1fffffffff 0xfffffff8ffffffff

def z64 : W := mkw 0x80922b190413854c 0x04049158c8209c2a 0xfefe3f1f8c7f87ff 0xfff7f1f8fc63fc3f

def z65 : W := mkw 0x0f359cecaa805213 0x9079ace765540290 0x8d79d8ee73807800 0x846bcec7739c03c0

def z66 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000011804801e0 0x300000008c02400f

def z67 : W := mkw 0x0080201000108108 0x0004010080008408 0xec8038107071f996 0xd76401c083838fcc

def z68 : W := mkw 0x070015802e011410 0x903800ac017008a0 0xef003f007f81980e 0x0f7801f803fc0cc0

def z69 : W := mkw 0x4000c06481884222 0x22000603240c4211 0x0101c0e183880669 0x28080e070c1c4033

def z70 : W := mkw 0x4040402241c862a0 0x2a020201120e4315 0x0000000043806000 0x00000000021c0300

def z71 : W := mkw 0x008222110000000c 0x0004111088000000 0x7286271180000001 0x7b9431388c000000

def z72 : W := mkw 0x0f359ccc80000013 0x0079ace664000000 0x8d79d8ee00000000 0x846bcec770000000

def z73 : W := mkw 0x0fb7bffdae81561f 0x907dbdffed740ab0 0xffffffff8f800609 0xfffffffffc7c0030

def z74 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xa30007e04f80661b 0xcd18003f027c0330

def z75 : W := mkw 0x0000002000804200 0x0000000100040210 0xa10000e04380661b 0xcd080007021c0330

def z76 : W := mkw 0x4740d5e6efc976b2 0xba3a06af377e4bb5 0xef41ffffffc9ffff 0xff7a0ffffffe4fff

def z77 : W := mkw 0x0000010004010400 0x0000000800200820 0x620027118c4987ff 0x7b1001388c624c3f

def z78 : W := mkw 0x878237912e13955c 0x943c11bc89709caa 0x7e863f11bc7f9fff 0x7bf431f88de3fcff

def z79 : W := mkw 0x072d00003a240000 0xc039680001d12000 0x56be00003c360004 0x02b5f00001e1b000

def z80 : W := mkw 0x87ef63117f7f854c 0xe43f7b188bfbfc2a 0xf7ffe711ffff87ff 0x7fbfff388ffffc3f

def z81 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0x8579c00073800000 0x042bce00039c0000

def z82 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x00002711800187f1 0x400001388c000c3f

def z83 : W := mkw 0x0080201000108108 0x0004010080008408 0x6080201000718196 0x5304010080038c0c

def z84 : W := mkw 0x0700148000000010 0x003800a400000000 0x8d0018e000000000 0x846800c700000000

def z85 : W := mkw 0x0000804480000002 0x0000040224000000 0xa141c0ff80000001 0xfd0a0e07fc000000

def z86 : W := mkw 0x4040402241c862a0 0x2a020201120e4315 0x0000000043c867fa 0x00000000021e433f

def z87 : W := mkw 0x8000010004138540 0x0400000800209c2a 0x000000000c378004 0x000000000061bc00

def z88 : W := mkw 0x87ef62117b7e814c 0xe43f7b108bdbf40a 0xf7ffc011fffe01ee 0x3fbffe008ffff00f

def z89 : W := mkw 0x072515a02e815610 0x903928ad01740ab0 0xffffffe07f81fe1f 0xffffffff03fc0ff0

def z90 : W := mkw 0x074055a06fc95610 0xb03a02ad037e4ab0 0xef41ffe07fc9fe1f 0xff7a0fff03fe4ff0

def z91 : W := mkw 0x872743012f0f0444 0xa4393a1809787822 0x1307c7018f8e0669 0x28983e380c7c7033

def z92 : W := mkw 0x072540002b0c0000 0xa0392a0001586000 0xf707c0007f8e000e 0x2fb83e0003fc7000

def z93 : W := mkw 0x0fffbedfd070a99f 0x487ffdf6fe83854c 0xffffffff80700181 0xfffffffffc03800c

def z94 : W := mkw 0x8002030104138544 0x0400101808209c2a 0x120607018c7f87ff 0x289030380c63fc3f

def z95 : W := mkw 0x0fffbedfd070a99f 0x487ffdf6fe83854c 0xfffffffff071f997 0xffffffffff838fcc

def z96 : W := mkw 0x07fd281a7a74a988 0xc83fe940d3d3a54c 0xfefe381e7c77f996 0xd7f7f1c0f3e3bfcc

def z97 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x528627000c378004 0x029431380061bc00

def z98 : W := mkw 0xc082e375859bc76e 0x2604171bac2cde3b 0x7387e7f18fff87ff 0x7b9c3f3f8c7ffc3f

def z99 : W := mkw 0x4ffffefffbec62bf 0xea7ffff7ffdf6315 0xfffffffffffe67ff 0xfffffffffffff33f

def z100 : W := mkw 0x8fb7bfdd8413855f 0x047dbdfeec209c2a 0xffffffff8c7f87ff 0xfffffffffc63fc3f

def z101 : W := mkw 0x07d83dba7ef1ff98 0xd83ec1edd3f78ffc 0xeff83ffe7ff1ff9f 0xdf7fc1fff3ff8ffc

def z102 : W := mkw 0x070015802e011410 0x903800ac017008a0 0x4e003f003c019804 0x027001f801e00cc0

def z103 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0x8141c0ee43c867fa 0x840a0e07721e433f

def z104 : W := mkw 0x40d0e87ec1c862aa 0x2a068743f60e4315 0xedf9f8ffc3c867fb 0xff6fcfc7fe1e433f

def z105 : W := mkw 0x000001202e815600 0x9000000901740ab0 0x000000007f81fe1e 0x0000000003fc0ff0

def z106 : W := mkw 0x08b7aa5d8000000f 0x0045bd52ec000000 0x10ffc01f80000000 0x3087fe00fc000000

def z107 : W := mkw 0x0000010004010400 0x0000000800200820 0x620027000c01861f 0x4b10013800600c30

def z108 : W := mkw 0x878237b12e93d75c 0x943c11bd89749eba 0xff863ff1ffffffff 0xfffc31ff8fffffff

def z109 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xa141c0ffc3806001 0xfd0a0e07fe1c0300

def z110 : W := mkw 0x07903c9800000018 0x003c81e4c0000000 0xeff83ffe00000001 0xdf7fc1fff0000000

def z111 : W := mkw 0x070000002a000000 0x8038000001500000 0xef0038007f81f81e 0xcf7801c003fc0fc0

def z112 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xfefe381e7c7ff99e 0xfff7f1c0f3e3ffcc

def z113 : W := mkw 0x072d00003a240000 0xc039680001d12000 0xf7ffc0003c360004 0x3fbffe0001e1b000

def z114 : W := mkw 0x0f2796c580000017 0x00793cb62c000000 0x1307c7e180000001 0x28983e3f0c000000

def z115 : W := mkw 0x070000002a000000 0x8038000001500000 0xe70000007f80000e 0x0f38000003fc0000

def z116 : W := mkw 0x4ff7ffffefc976bf 0xba7fbfffff7e4bb5 0xffffffffffc9ffff 0xfffffffffffe4fff

def z117 : W := mkw 0x0892bedd8000001f 0x004495f6ec000000 0x08003fff80000001 0xc04001fffc000000

def z118 : W := mkw 0x4ff7feffc1c862bf 0x2a7fbff7fe0e4315 0xffffffffc3c867fb 0xfffffffffe1e433f

def z119 : W := mkw 0x00da2a1b5070a98c 0x4806d150da83854c 0xfefe3f1ff071f997 0xfff7f1f8ff838fcc

def z120 : W := mkw 0x8000010004138540 0x0400000800209c2a 0x000000000c7f87fe 0x000000000063fc3f

def z121 : W := mkw 0x0f379ecd80000017 0x0079bcf66c000000 0x9f7fdfef80000001 0xacfbfeff7c000000

def z122 : W := mkw 0x4058c86ed1e86aa2 0x6a02c643768f4355 0xad79d8fff3c87ffb 0xfd6bcec7ff9e43ff

def z123 : W := mkw 0x4000c06481884222 0x22000603240c4211 0x2101c0f183c807fb 0x79080e078c1e403f

def z124 : W := mkw 0x072555a02f8d5610 0xb0392aad017c6ab0 0x1307c7e00f8e0609 0x28983e3f007c7030

def z125 : W := mkw 0x076d54a07bec5210 0xf03b6aa503df6290 0xffffd8e07ffe780e 0xbffffec703fff3c0

def z126 : W := mkw 0x0090281a0010a988 0x08048140d000854c 0xecf8381e0001f990 0xd767c1c0f0000fcc

def z127 : W := mkw 0x0090281800108108 0x00048140c0008408 0xecf8381e00718196 0xd767c1c0f0038c0c

def z128 : W := mkw 0x4040c046c14820a2 0x2a020602360a4105 0x0041c01f804801e0 0x30020e00fc02400f

def z129 : W := mkw 0x40d8e87ed1f8ebaa 0x6a06c743f68fc75d 0xedf9f8fff3f9ffff 0xff6fcfc7ff9fcfff

def z130 : W := mkw 0x076d54a07bec5210 0xf03b6aa503df6290 0x8d79d8e073807800 0x846bcec7039c03c0

def z131 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0x8d003fe07381fe11 0xc46801ff039c0ff0

def z132 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x620027118c0187ff 0x4b1001388c600c3f

def z133 : W := mkw 0x070014a02a805210 0x903800a501540290 0xef003fe073807801 0xcf7801ff039c03c0

def z134 : W := mkw 0x0f351c8800000011 0x0079a8e440000000 0x0c38180000000000 0x0061c0c000000000

def z135 : W := mkw 0x0080201000108108 0x0004010080008408 0x0000201000018190 0x4000010080000c0c

def z136 : W := mkw 0x0000000000000000 0x0000000000000000 0x120600000c0e0008 0x2890300000607000

def z137 : W := mkw 0x808222110012814c 0x040411108800940a 0x10860011807e01e0 0x308430008c03f00f

def z138 : W := mkw 0x80da2b1b5473adcc 0x4c06d158daa39d6e 0xfefe3f1ffc7fffff 0xfff7f1f8ffe3ffff

def z139 : W := mkw 0x0000000000000000 0x0000000000000000 0x10860000007e0000 0x308430000003f000

def z140 : W := mkw 0x000015a02e815610 0x900000ad01740ab0 0x08003fe07f81fe1f 0xc04001ff03fc0ff0

def z141 : W := mkw 0x0f2594c480000013 0x00792ca624000000 0x0101c0e000000000 0x00080e0700000000

def z142 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xecf8381ff079ffff 0xff67c1c0ff83cfff

def z143 : W := mkw 0x0000400001080000 0x2000020000084000 0x0101c00003880008 0x28080e00001c4000

def z144 : W := mkw 0xc0c2e357c55ba5ee 0x2e06171abe2add2f 0x72c7e71f8c7f87ff 0x7b963f38fc63fc3f

def z145 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x728627000c37861f 0x4b9431380061bc30

def z146 : W := mkw 0x0fff7e997b6c001d 0xe07ffbf4cbdb6000 0xffffff007ffe000e 0x3ffffff803fff000

def z147 : W := mkw 0x074800007a600000 0xc03a400003d30000 0xe7f800007ff0000e 0x1f3fc00003ff8000

def z148 : W := mkw 0x0098281810308908 0x4004c140c0818448 0x4cb8380030319804 0x0265c1c001818cc0

def z149 : W := mkw 0x07fd681a7b7ca988 0xe83feb40d3dbe54c 0xfffff81e7ffff99e 0xffffffc0f3ffffcc

def z150 : W := mkw 0x070000002a000000 0x8038000001500000 0x460000003c000004 0x0230000001e00000

def z151 : W := mkw 0x4040402241c862a0 0x2a020201120e4315 0xa10000e043c867fb 0xcd080007021e433f

def z152 : W := mkw 0x008222110000000c 0x0004111088000000 0x5286270000000000 0x0294313800000000

def z153 : W := mkw 0x87ef63117f7f854c 0xe43f7b188bfbfc2a 0xf7ffe7007fff800e 0x3fbfff3803fffc00

def z154 : W := mkw 0x07fd7dba7ffdff98 0xf83febedd3ffeffc 0xfffffffe7fffff9f 0xfffffffff3fffffc

def z155 : W := mkw 0x0000012004815600 0x1000000900240ab0 0x000000000001fe10 0x0000000000000ff0

def z156 : W := mkw 0x0000000000000000 0x0000000000000000 0x728600118c7e07ff 0x7b9430008c63f03f

def z157 : W := mkw 0x808237b10493d75c 0x140411bd88249eba 0x7a863ff18c7fffff 0xfbd431ff8c63ffff

def z158 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x000027118c7f87ff 0x400001388c63fc3f

def z159 : W := mkw 0x0fb73e990000001d 0x007db9f4c8000000 0x5ebe3f0000000000 0x02f5f1f800000000

def z160 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000001000400192 0x510000008002000c

def z161 : W := mkw 0x070000002a000000 0x8038000001500000 0x8500000073800000 0x04280000039c0000

def z162 : W := mkw 0x00d83dba54f1ff98 0x5806c1edd2a78ffc 0xecf83ffe7071ff97 0xd767c1fff3838ffc

def z163 : W := mkw 0x078035b02e91d718 0x903c01ad81748eb8 0xef803ff07ff1ff9f 0xdf7c01ff83ff8ffc

def z164 : W := mkw 0x07581daa7ee17e90 0xd83ac0ed53f70bf4 0xef783fee7f81fe1f 0xcf7bc1ff73fc0ff0

def z165 : W := mkw 0x0725148000000010 0x003928a400000000 0xffffffe000000001 0xffffffff00000000

def z166 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0x4e003f007f81fe1e 0x027001f803fc0ff0

def z167 : W := mkw 0x0000002000804200 0x0000000100040210 0x810000e043806000 0x84080007021c0300

def z168 : W := mkw 0x0f359ccc80000013 0x0079ace664000000 0xef79ffee00000001 0xcf7bcfff70000000

def z169 : W := mkw 0xc082a3778493e7ee 0x0e04151bbc249f3f 0x728627ff8c7fe7ff 0xfb94313ffc63ff3f

def z170 : W := mkw 0x076d40027b6c2080 0xe83b6a0013db6104 0xf7ffc01e7ffe619e 0xffbffe00f3fff30c

def z171 : W := mkw 0x808222110012814c 0x040411108800940a 0x728600118c7e01ee 0x3b9430008c63f00f

def z172 : W := mkw 0x004800025070a980 0x480240001283854c 0xe4f800007071f996 0x1727c00003838fcc

def z173 : W := mkw 0x0040400041480000 0x20020200020a4000 0x8141c00043800000 0x040a0e00021c0000

def z174 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffff8c7e000f 0xfffffffffc63f000

def z175 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0x8141c0ee43806000 0x840a0e07721c0300

def z176 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0x00f8001e00700180 0x1007c000f003800c

def z177 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0x1307c0007ffe000e 0x28983e0003fff000

def z178 : W := mkw 0x808222110012814c 0x040411108800940a 0x00000011800001e0 0x000000008c00000f

def z179 : W := mkw 0x40008066808062a2 0x0a00040334040315 0x000000ff800067f1 0xc0000007fc00033f

def z180 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0x00f8001e7071f996 0x1007c000f3838fcc

def z181 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xa141c0ee4380661b 0xcd0a0e07721c0330

def z182 : W := mkw 0x070095e4ae815612 0x903804af25740ab0 0xef41ffffff81fe1f 0xff7a0ffffffc0ff0

def z183 : W := mkw 0x8fb73f990413855d 0x047db9fcc8209c2a 0x7ebe3f118c7f87ff 0x7bf5f1f88c63fc3f

def z184 : W := mkw 0x8fb73f990413855d 0x047db9fcc8209c2a 0x5ebe3f000c378004 0x02f5f1f80061bc00

def z185 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000011804807fb 0x790000008c02403f

def z186 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xed41f8fff3c9ffff 0xff6a0fc7ff9e4fff

def z187 : W := mkw 0x0040000240402080 0x0802000012020104 0x0040001e00400180 0x10020000f002000c

def z188 : W := mkw 0x40d8e87ed1f8ebaa 0x6a06c743f68fc75d 0xa1f9c0ffc3f867fb 0xfd0fce07fe1fc33f

def z189 : W := mkw 0x0048000050600000 0x4002400002830000 0xe4f8000070700006 0x1727c00003838000

def z190 : W := mkw 0x0090281800000008 0x00048140c0000000 0x0800381e00000000 0xc04001c0f0000000

def z191 : W := mkw 0xc7c2f7f7efdbf7fe 0xbe3e17bfbf7edfbf 0xffc7ffffffffffff 0xfffe3fffffffffff

def z192 : W := mkw 0x48f7ea5fc14820af 0x2a47bf52fe0a4105 0x10ffc01f804801e0 0x3087fe00fc02400f

def z193 : W := mkw 0xc0c2e257c15aa1ee 0x2e061712be0ad50f 0x10c7c01f807e01e0 0x30863e00fc03f00f

def z194 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0x0b003fe00f81fe19 0xc85801ff007c0ff0

def z195 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x728627100c778196 0x539431388063bc0c

def z196 : W := mkw 0x8fb7bedd8012815f 0x047dbdf6ec00940a 0xffffffff807e01e1 0xfffffffffc03f00f

def z197 : W := mkw 0x4000c06481884222 0x22000603240c4211 0x0101c0e003800000 0x00080e07001c0000

def z198 : W := mkw 0x4ff7fedfc14820bf 0x2a7fbff6fe0a4105 0xffffffff804801e1 0xfffffffffc02400f

def z199 : W := mkw 0xc0c2e277c1dae3ee 0x2e061713be0ed71f 0xb1c7c0ffc3fe67fb 0xfd8e3e07fe1ff33f

def z200 : W := mkw 0x000001202e815600 0x9000000901740ab0 0x000000000f800608 0x00000000007c0030

def z201 : W := mkw 0x8fa7b7d58413855f 0x047d3dbeac209c2a 0x7387e7f18c7f87ff 0x7b9c3f3f8c63fc3f

def z202 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xccf8380e7031f804 0x8667c1c073818fc0

def z203 : W := mkw 0x0827824580000007 0x00413c122c000000 0x1007c00180000000 0x20803e000c000000

def z204 : W := mkw 0x07581caa7ae07a90 0xd83ac0e553d703d4 0x8d7818ee73807800 0x846bc0c7739c03c0

def z205 : W := mkw 0x070014a02a805210 0x903800a501540290 0xef0018e07f80780e 0x8f7800c703fc03c0

def z206 : W := mkw 0x0090281800108908 0x00048140c0008448 0x0800380000019800 0x004001c000000cc0

def z207 : W := mkw 0x0000010004010400 0x0000000800200820 0xee003f007c01fe1f 0xcf7001f803e00ff0

def z208 : W := mkw 0x07d83cba7af0fb98 0xd83ec1e5d3d787dc 0xedf838fe73f1f996 0xd76fc1c7f39f8fcc

def z209 : W := mkw 0x804841007f7f8540 0xe402420803fbfc2a 0x000000007fff87fe 0x0000000003fffc3f

def z210 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xfffff8007ffff81e 0xffffffc003ffffc0

def z211 : W := mkw 0x0f7ddcccfb6c0013 0xe07beee667db6000 0xffffd8ee7ffe000e 0xbffffec773fff000

def z212 : W := mkw 0x0f7ddcccfb6c0013 0xe07beee667db6000 0x8d79d8ee73800000 0x846bcec7739c0000

def z213 : W := mkw 0x070015802e011410 0x903800ac017008a0 0x6e003f003c019e1f 0x4b7001f801e00cf0

def z214 : W := mkw 0x809a2b1914338d4c 0x4404d158c8a19c6a 0x5ebe3f003c379804 0x02f5f1f801e1bcc0

def z215 : W := mkw 0x4f75dceec1c862b3 0x2a7baee7760e4315 0x8d79d8ee43806000 0x846bcec7721c0300

def z216 : W := mkw 0x07ef62117b6c000c 0xe03f7b108bdb6000 0xf7ffe711fffe000f 0x7fbfff388ffff000

def z217 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0x13ffc7ff80000001 0x389ffe3ffc000000

def z218 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffff804807fb 0xfffffffffc02403f

def z219 : W := mkw 0x4fb7fefd8188423f 0x227dbff7ec0c4211 0xffffffff83880669 0xfffffffffc1c4033

def z220 : W := mkw 0x80922b1b0413adcc 0x0c049158d8209d6e 0x08003f1f8001fff1 0xc04001f8fc000fff

def z221 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xd7ffc0007fb60004 0x06bffe0003fdb000

def z222 : W := mkw 0x80da2a1b5072a9cc 0x4c06d150da83954e 0x10fe001f807e01e0 0x3087f000fc03f00f

def z223 : W := mkw 0x0f2797e5ae815617 0x90793cbf2d740ab0 0x1307c7e18f800609 0x28983e3f0c7c0030

def z224 : W := mkw 0x0fffea5dfb6c000f 0xe07fff52efdb6000 0xf7ffc01ffffe000e 0x3fbffe00fffff000

def z225 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c00380030019804 0x026001c001800cc0

def z226 : W := mkw 0x07b5281800000008 0x003da940c0000000 0xfffff81e00000000 0xffffffc0f0000000

def z227 : W := mkw 0x4040d5e6c5c976b2 0x3a0206af362e4bb5 0xa941ffffc3c9fffb 0xfd4a0ffffe1e4fff

def z228 : W := mkw 0x00d8291a5471ad88 0x4806c148d2a38d6c 0xeef83f1e7c71ff9f 0xdf77c1f8f3e38ffc

def z229 : W := mkw 0x008222110000000c 0x0004111088000000 0x728627118c7e000f 0x7b9431388c63f000

def z230 : W := mkw 0x008223110401040c 0x0004111888200820 0x728627118c01861f 0x7b9431388c600c30

def z231 : W := mkw 0x0040000040400000 0x0002000002020000 0xa040000040400002 0x1502000002020000

def z232 : W := mkw 0x08b7bedd8000001f 0x0045bdf6ec000000 0x18ffffff80000001 0xf0c7fffffc000000

def z233 : W := mkw 0x070014a02a805210 0x903800a501540290 0x8d0018e073807800 0x846800c7039c03c0

def z234 : W := mkw 0x878237b12e93d75c 0x943c11bd89749eba 0xef003ff1ff81ffff 0xcf7801ff8ffc0fff

def z235 : W := mkw 0x07bd28183a348908 0xc03de940c1d1a448 0x5ebe38003c379804 0x02f5f1c001e1bcc0

def z236 : W := mkw 0x08b7aa5d8000000f 0x0045bd52ec000000 0xfcfff81f80000000 0xf7e7ffc0fc000000

def z237 : W := mkw 0x076d40027b7ca980 0xe83b6a0013dbe54c 0xf7ffc0007ffff99e 0x3fbffe0003ffffcc

def z238 : W := mkw 0x0040400041480000 0x20020200020a4000 0x0000000043c8000a 0x00000000021e4000

def z239 : W := mkw 0x8002030104030444 0x0400101808201822 0x120607000c060000 0x0090303800603000

def z240 : W := mkw 0x0080201000108108 0x0004010080008408 0x728620100c7f819e 0x7b9431008063fc0c

def z241 : W := mkw 0x40c0e076c1d8e3aa 0x2a060703b60ec71d 0xe1c1e0ffc3f9e7ff 0xff0e0f07fe1fcf3f

def z242 : W := mkw 0x876f43017f6f0444 0xe43b7a180bfb7822 0xf7ffc701fffe066f 0x3fbffe380ffff033

def z243 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xe779c0007f80000e 0x0f3bce0003fc0000

def z244 : W := mkw 0x0ff7feddc148001f 0x207fbff6ee0a4000 0xffffffffc3c8000b 0xfffffffffe1e4000

def z245 : W := mkw 0x0725000000000000 0x0039280000000000 0xf7ffc0000c7e000e 0x3fbffe000063f000

def z246 : W := mkw 0x876d41007f7f8540 0xe43b6a0803fbfc2a 0xf7ffc0007fff87fe 0x3fbffe0003fffc3f

def z247 : W := mkw 0x0000010004010400 0x0000000800200820 0x0000270000018611 0x4000013800000c30

def z248 : W := mkw 0x08923e990000001d 0x004491f4c8000000 0x08003f0000000000 0x004001f800000000

def z249 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0x8579c0007ffe000e 0x042bce0003fff000

def z250 : W := mkw 0x0fbf3e991030891d 0x407df9f4c8818448 0x5ebe3f0030319804 0x02f5f1f801818cc0

def z251 : W := mkw 0x80ef6311557f854c 0x64077b188aabfc2a 0x72ffe7118c7f87ff 0x7b97ff388c63fc3f

def z252 : W := mkw 0x4040c046c14820a2 0x2a020602360a4105 0x2041c01f804807fb 0x79020e00fc02403f

def z253 : W := mkw 0xc040412245dbe7e0 0x2e020209122edf3f 0x000000004fffe7fe 0x00000000027fff3f

def z254 : W := mkw 0x4048c066d1f8eba2 0x6a024603368fc75d 0xa141c0fff3f9ffff 0xfd0a0e07ff9fcfff

def z255 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xff863fe07ffffe1f 0xfffc31ff03fffff0

def z256 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xcf003fe07f81f804 0x867801ff03fc0fc0

def z257 : W := mkw 0x00d8283a50f0eb88 0x4806c141d287875c 0xedf838fe73f1ff9f 0xdf6fc1c7f39f8ffc

def z258 : W := mkw 0x0090281800000008 0x00048140c0000000 0xecf8381e7001f816 0xd767c1c0f3800fc0

def z259 : W := mkw 0x404840227bec62a0 0xea02420113df6315 0x000000007ffe67fe 0x0000000003fff33f

def z260 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0x4cb838007071f996 0x0265c1c003838fcc

def z261 : W := mkw 0x4040c064c1c84222 0x22020603260e4211 0xa141c0e1c3c8066b 0x3d0a0e070e1e4033

def z262 : W := mkw 0x000001002e011400 0x90000008017008a0 0x000000003c019804 0x0000000001e00cc0

def z263 : W := mkw 0x004800025070a980 0x480240001283854c 0xec0038007071f996 0xc76001c003838fcc

def z264 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0x8141c0ffc3c861e0 0xb40a0e07fe1e430f

def z265 : W := mkw 0x40d8e87ed1f8ebaa 0x6a06c743f68fc75d 0xedf9f8fe73f1f996 0xd76fcfc7f39f8fcc

def z266 : W := mkw 0x80ca23115473854c 0x440651188aa39c2a 0xf6fe2711fc7f87ff 0x7fb7f1388fe3fc3f

def z267 : W := mkw 0x0080201000108108 0x0004010080008408 0x4080200000318004 0x0204010000018c00

def z268 : W := mkw 0x870217a12e835654 0x943810bd09741ab2 0xff063fe1ff8ffe7f 0xeff831ff0ffc7ff3

def z269 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x72862711800187f1 0x7b9431388c000c3f

def z270 : W := mkw 0x074815a27ef1ff90 0xd83a40ad13f78ffc 0xef003fe07ff1ff9f 0xcf7801ff03ff8ffc

def z271 : W := mkw 0x8080211004138548 0x0404010880209c2a 0x608020100c7f87fe 0x530401008063fc3f

def z272 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x728627000c7f800e 0x3b9431380063fc00

def z273 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0x13ffc0000ffe0008 0x389ffe00007ff000

def z274 : W := mkw 0x074015a26ec17690 0x983a00ad13760bb4 0xef403ffe7fc1ff9f 0xdf7a01fff3fe0ffc

def z275 : W := mkw 0x8fb7bfdd8403045f 0x047dbdfeec201822 0xffffffff8c0e0669 0xfffffffffc607033

def z276 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x0000270000018000 0x0000013800000c00

def z277 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xef003ff1ffc9ffff 0xff7801ff8ffe4fff

def z278 : W := mkw 0x0fbfbedd9030891f 0x407dfdf6ec818448 0xffffffffb0319805 0xfffffffffd818cc0

def z279 : W := mkw 0x000800003a240000 0xc000400001d12000 0x000000003c360004 0x0000000001e1b000

def z280 : W := mkw 0x0892bedd8000001f 0x004495f6ec000000 0x7a863fff80000001 0xfbd431fffc000000

def z281 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xdfffffee00000000 0x86ffffff70000000

def z282 : W := mkw 0x0040400041480000 0x20020200020a4000 0xf3c7c0004ffe000e 0x3f9e3e00027ff000

def z283 : W := mkw 0x474055a26fc976b0 0xba3a02ad137e4bb5 0xef003fe07fc9ffff 0xcf7801ff03fe4fff

def z284 : W := mkw 0x808223110413854c 0x0404111888209c2a 0xfe863f11fc7fffff 0xfff431f88fe3ffff

def z285 : W := mkw 0x87a763112f1f854c 0xa43d3b188978fc2a 0x7387e7118fff87ff 0x7b9c3f388c7ffc3f

def z286 : W := mkw 0x4000c06481884222 0x22000603240c4211 0xa141c0ff83880669 0xfd0a0e07fc1c4033

def z287 : W := mkw 0x072500002a000000 0x8039280001500000 0xf7ffc0007f80000e 0x3fbffe0003fc0000

def z288 : W := mkw 0x40404002414820a0 0x2a020200120a4105 0x00000000004801e0 0x000000000002400f

def z289 : W := mkw 0x0000804480000002 0x0000040224000000 0xa141c0ff804807fb 0xfd0a0e07fc02403f

def z290 : W := mkw 0x4f67d6e7c1c862b7 0x2a7b3eb73e0e4315 0xb347c7ffc3c867fb 0xfd9a3e3ffe1e433f

def z291 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x10862711807f87f1 0x708431388c03fc3f

def z292 : W := mkw 0x87ef77b17fffd75c 0xf43f7bbd8bfffeba 0xfffffff1ffffffff 0xffffffff8fffffff

def z293 : W := mkw 0x476dc066fbec62a2 0xea3b6e0337df6315 0xa579c0fff3c867fb 0xfd2bce07ff9e433f

def z294 : W := mkw 0x0058080a50602880 0x4802c04052830144 0xac78181e70407992 0xd563c0c0f38203cc

def z295 : W := mkw 0x0090281800000008 0x00048140c0000000 0x00f8001e00000000 0x1007c000f0000000

def z296 : W := mkw 0x0fb73f992e01141d 0x907db9fcc97008a0 0x5ebe3f003c019804 0x02f5f1f801e00cc0

def z297 : W := mkw 0x0040c044c1480002 0x20020602260a4000 0xa141c0ffc3c8000b 0xfd0a0e07fe1e4000

def z298 : W := mkw 0x0000000000000000 0x0000000000000000 0xa040001e00000000 0xd5020000f0000000

def z299 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xf7ffc011fffe07ff 0x7fbffe008ffff03f

def z300 : W := mkw 0x080296c580000017 0x004014b62c000000 0x000007e180000001 0x0000003f0c000000

def z301 : W := mkw 0x072540002b0c0000 0xa0392a0001586000 0x7387c0000ffe000e 0x3b9c3e00007ff000

def z302 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xe5f9c00073f00006 0x172fce00039f8000

def z303 : W := mkw 0x878223112e13854c 0x843c111889709c2a 0xf7862711ffff87ff 0x7fbc31388ffffc3f

def z304 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0x56ffc0003c7e0004 0x32b7fe0001e3f000

def z305 : W := mkw 0xc7efe377ffffe7ee 0xee3f7f1bbfffff3f 0xf7ffe7ffffffe7ff 0xffbfff3fffffff3f

def z306 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0x08f8381e0071f990 0xd047c1c0f0038fcc

def z307 : W := mkw 0x076d54807b6c0010 0xe03b6aa403db6000 0xffffffe07ffe000f 0xffffffff03fff000

def z308 : W := mkw 0x0008000010308900 0x4000400000818448 0x0000000030319804 0x0000000001818cc0

def z309 : W := mkw 0x076d40207bec4200 0xe03b6a0103df6210 0xf7ffc0e07ffe661f 0xffbffe0703fff330

def z310 : W := mkw 0x070001002e010400 0x8038000801700820 0xe70027007f81861f 0x4f38013803fc0c30

def z311 : W := mkw 0x0f2796c580000017 0x00793cb62c000000 0xb347c7ff80000001 0xfd9a3e3ffc000000

def z312 : W := mkw 0x4040c046c14820a2 0x2a020602360a4105 0x0041c00e00000000 0x00020e0070000000

def z313 : W := mkw 0x0000002000804200 0x0000000100040210 0x010000e003800609 0x08080007001c0030

def z314 : W := mkw 0x4058c86ed1e86aa2 0x6a02c643768f4355 0x8d79d8ee73807800 0x846bcec7739c03c0

def z315 : W := mkw 0x070014a02a805210 0x903800a501540290 0xad0018e073807e1b 0xcd6800c7039c03f0

def z316 : W := mkw 0x8000010004030440 0x0400000800201822 0x000000000c0e0668 0x0000000000607033

def z317 : W := mkw 0x0fb7beddaa00001f 0x807dbdf6ed500000 0xffffffffff80000f 0xfffffffffffc0000

def z318 : W := mkw 0x0000000000000000 0x0000000000000000 0xa10000004380000a 0x0d080000021c0000

def z319 : W := mkw 0x006d4000516c0000 0x60036a00028b6000 0xf4ffc000707e0006 0x37a7fe000383f000

def z320 : W := mkw 0x08ffaa5fd070a98f 0x4847fd52fe83854c 0x10ffc01f80700180 0x3087fe00fc03800c

def z321 : W := mkw 0x070015a004815610 0x103800ad00240ab0 0xef003fe00001fe11 0xcf7801ff00000ff0

def z322 : W := mkw 0x4040402241c862a0 0x2a020201120e4315 0xa141c00043c867fa 0x3d0a0e00021e433f

def z323 : W := mkw 0x4740d4e6c1c862b2 0x2a3a06a7360e4315 0xef41ffffc3c867fb 0xff7a0ffffe1e433f

def z324 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xa0f8001e40706192 0xd507c000f203830c

def z325 : W := mkw 0x0fbf3e993a24001d 0xc07df9f4c9d12000 0x5ebe3f003c360004 0x02f5f1f801e1b000

def z326 : W := mkw 0x070015802e011410 0x903800ac017008a0 0xef003fe03c019805 0xcf7801ff01e00cc0

def z327 : W := mkw 0x0f359ccc80000013 0x0079ace664000000 0xad79d8ff80000001 0xfd6bcec7fc000000

def z328 : W := mkw 0x4048c066d1e862a2 0x6a024603368f4315 0xe5f9c0fff3f867ff 0xff2fce07ff9fc33f

def z329 : W := mkw 0x0040000240402080 0x0802000012020104 0xa040001fc04867fb 0xfd020000fe02433f

def z330 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x528627118c3787f5 0x429431388c61bc3f

def z331 : W := mkw 0x0892bedd8000001f 0x004495f6ec000000 0xecf83fff80000001 0xd767c1fffc000000

def z332 : W := mkw 0x004841207fed5600 0xf002420903ff6ab0 0x000000007ffffe1e 0x0000000003fffff0

def z333 : W := mkw 0x4fb7beff808062bf 0x0a7dbdf7fc040315 0xffffffff800067f1 0xfffffffffc00033f

def z334 : W := mkw 0x072555a02f8d5610 0xb0392aad017c6ab0 0xff07ffe07f8ffe1f 0xeff83fff03fc7ff0

def z335 : W := mkw 0x076d55807f6d1410 0xf03b6aac03fb68a0 0xffffff007fff980e 0x3ffffff803fffcc0

def z336 : W := mkw 0x07ed60107b7c8108 0xe03f6b0083dbe408 0xf7ffe0107fff819e 0x7fbfff0083fffc0c

def z337 : W := mkw 0x0000010004010400 0x0000000800200820 0x728627000c7f861f 0x7b9431380063fc30

def z338 : W := mkw 0x40d8e85ed178a9aa 0x6a06c742f68bc54d 0xecf9f81ff079f9f6 0xf767cfc0ff83cfcf

def z339 : W := mkw 0x08b72a190000000d 0x0045b950c8000000 0x10be000000000000 0x0085f00000000000

def z340 : W := mkw 0x808223310493c74c 0x0404111988249e3a 0xf38627f1cfffe7ff 0xff9c313f8e7fff3f

def z341 : W := mkw 0x0048000250602080 0x4802400012830104 0xe4f8001e70706196 0xd727c000f383830c

def z342 : W := mkw 0x0fbfbeddba24001f 0xc07dfdf6edd12000 0xffffffffbc360005 0xfffffffffde1b000

def z343 : W := mkw 0x80da2b1b5473adcc 0x4c06d158daa39d6e 0xecf83f1ff071fff7 0xd767c1f8ff838fff

def z344 : W := mkw 0x0fb7feddab0c001f 0xa07dbff6ed586000 0xffffffff8f8e0009 0xfffffffffc7c7000

def z345 : W := mkw 0x808223110403044c 0x0404111888201822 0x728627118c0e0669 0x7b9431388c607033

def z346 : W := mkw 0xc042c367c5cb66e6 0x2e02161b3e2e5b37 0xb347c7ffcfce67fb 0xfd9a3e3ffe7e733f

def z347 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0x60f8201e00718196 0x5307c100f0038c0c

def z348 : W := mkw 0x0700148000000010 0x003800a400000000 0x4e003f0000000000 0x027001f800000000

def z349 : W := mkw 0x0f7d9cced0602893 0x487bece676830144 0x8d79d8ee70007800 0x846bcec7738003c0

def z350 : W := mkw 0x88b7ab5d8413854f 0x0445bd5aec209c2a 0x72ffe71f8c7f87ff 0x7b97ff38fc63fc3f

def z351 : W := mkw 0x8002030104030444 0x0400101808201822 0x120607018c0e0669 0x289030380c607033

def z352 : W := mkw 0x808223312e93d74c 0x9404111989749eba 0x72862711ffffffff 0x7b9431388fffffff

def z353 : W := mkw 0x40d8a87ed0f0ebaa 0x4a06c543f687875d 0xecf838fff071fff7 0xd767c1c7ff838fff

def z354 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xf3c7c0ffcffe67ff 0xff9e3e07fe7ff33f

def z355 : W := mkw 0x0090281800000008 0x00048140c0000000 0x4cb8380000000000 0x0265c1c000000000

def z356 : W := mkw 0x076d000050600000 0x403b680002830000 0xf7ffc00070700006 0x3fbffe0003838000

def z357 : W := mkw 0x0098281810308908 0x4004c140c0818448 0xecb838007031f816 0xc765c1c003818fc0

def z358 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0x8141c0ffc38067f1 0xc40a0e07fe1c033f

def z359 : W := mkw 0x0000000000000000 0x0000000000000000 0xec00380000000000 0xc76001c000000000

def z360 : W := mkw 0x0000012004814600 0x0000000900240a30 0xe30027e04f81e61f 0xcf18013f027c0f30

def z361 : W := mkw 0x0080201000108108 0x0004010080008408 0x0080001000700180 0x100400008003800c

def z362 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xe70007e07f80060f 0x0f38003f03fc0030

def z363 : W := mkw 0x07983db83eb1df18 0xd03cc1edc1f58ef8 0xefb83fe07fb1fe1f 0xcf7dc1ff03fd8ff0

def z364 : W := mkw 0x0fb7befdaa80521f 0x907dbdf7ed540290 0xfffffffff3807801 0xffffffffff9c03c0

def z365 : W := mkw 0x80da2b1b5473adcc 0x4c06d158daa39d6e 0x72fe271f8c7f87ff 0x7b97f138fc63fc3f

def z366 : W := mkw 0x0040400241482080 0x28020200120a4104 0xa141c01e43c8619a 0xfd0a0e00f21e430c

def z367 : W := mkw 0x80c223134453a5cc 0x0c0611189a229d2e 0xf2c6271fcc7fe7ff 0xff963138fe63ff3f

def z368 : W := mkw 0x070094c480000012 0x003804a624000000 0xef41ffff80000001 0xff7a0ffffc000000

def z369 : W := mkw 0x0700148000000010 0x003800a400000000 0x030007e000000001 0x0818003f00000000

def z370 : W := mkw 0x072d00003a240000 0xc039680001d12000 0xf7be00007fb6000e 0x0fbdf00003fdb000

def z371 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000001180000001 0x790000008c000000

def z372 : W := mkw 0x808222110012814c 0x040411108800940a 0x70862011807f81f6 0x738431008c03fc0f

def z373 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0x0101c0e1c3c867fb 0x28080e070e1e433f

def z374 : W := mkw 0x006d4000516c0000 0x60036a00028b6000 0xb1ffc00043fe000a 0x3d8ffe00021ff000

def z375 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0x4e003fe03c01fe15 0xc27001ff01e00ff0

def z376 : W := mkw 0x406dc046d16c20a2 0x6a036e02368b6105 0x10ffc01f807e01e0 0x3087fe00fc03f00f

def z377 : W := mkw 0x8fb7bffdae93d75f 0x947dbdffed749eba 0xffffffffffffffff 0xffffffffffffffff

def z378 : W := mkw 0x88b7aa5d8012814f 0x0445bd52ec00940a 0x10ffc01f807e01e0 0x3087fe00fc03f00f

def z379 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x60802711807187f7 0x530401388c038c3f

def z380 : W := mkw 0x809a2b1914338d4c 0x4404d158c8a19c6a 0x7ebe3f11bc7f9fff 0x7bf5f1f88de3fcff

def z381 : W := mkw 0x808237b10493d75c 0x140411bd88249eba 0x08003ff18001fff1 0xc04001ff8c000fff

def z382 : W := mkw 0x070000202a804200 0x8038000101540210 0xe70000e07f80661f 0xcf38000703fc0330

def z383 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0x8d79ffff80000001 0xc46bcffffc000000

def z384 : W := mkw 0x0058080a50602880 0x4802c04052830144 0xecf8180e70707806 0x9767c0c0738383c0

def z385 : W := mkw 0x0000806480804202 0x0000040324040210 0xa141c0ffc380661b 0xfd0a0e07fe1c0330

def z386 : W := mkw 0x074855a07fed5610 0xf03a42ad03ff6ab0 0xef003fe07ffffe1f 0xcf7801ff03fffff0

def z387 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x528627018c3f866d 0x2a9431380c61fc33

def z388 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0x5ebe3fff80000001 0xc2f5f1fffc000000

def z389 : W := mkw 0x0fb73e990000001d 0x007db9f4c8000000 0x7ebe3f1180000001 0x7bf5f1f88c000000

def z390 : W := mkw 0x00903dba0491ff98 0x180481edd0248ffc 0x08003ffe0001ff91 0xc04001fff0000ffc

def z391 : W := mkw 0x87da3fbb7ef3ffdc 0xdc3ed1fddbf79ffe 0xfffe3fffffffffff 0xfffff1ffffffffff

def z392 : W := mkw 0x4000c066818862a2 0x2a000603340c4315 0x0101c0ff838867f9 0xe8080e07fc1c433f

def z393 : W := mkw 0xc082a3778493e7ee 0x0e04151bbc249f3f 0x000027ff8001e7f1 0xc000013ffc000f3f

def z394 : W := mkw 0x072d00003a240000 0xc039680001d12000 0x76be00003c7e000e 0x3bb5f00001e3f000

def z395 : W := mkw 0x0048000050600000 0x4002400002830000 0x0000000070700006 0x0000000003838000

def z396 : W := mkw 0x0048000250602880 0x4802400012830144 0x0000000070007800 0x00000000038003c0

def z397 : W := mkw 0x0fa7b6d58000001f 0x007d3db6ac000000 0x7387e7f180000001 0x7b9c3f3f8c000000

def z398 : W := mkw 0x0fb7aa5d8000000f 0x007dbd52ec000000 0xf7ffc01f80000000 0x3fbffe00fc000000

def z399 : W := mkw 0x0000000000000000 0x0000000000000000 0x7286000000000000 0x3b94300000000000

def z400 : W := mkw 0x8000010004138540 0x0400000800209c2a 0x728600000c7f87fe 0x3b9430000063fc3f

def z401 : W := mkw 0x0058080a5070a980 0x4802c0405283854c 0x8c78180e7071f996 0x8463c0c073838fcc

def z402 : W := mkw 0x0048000050600000 0x4002400002830000 0x8478000070000000 0x0423c00003800000

def z403 : W := mkw 0x0090a85c8000000a 0x00048542e4000000 0xedf9f8ff80000001 0xff6fcfc7fc000000

def z404 : W := mkw 0x070000002a000000 0x8038000001500000 0xf78600007ffe000e 0x3fbc300003fff000

def z405 : W := mkw 0x8000010004138540 0x0400000800209c2a 0x00000000000187f0 0x0000000000000c3f

def z406 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000007001f816 0x0000000003800fc0

def z407 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000004807fa 0x000000000002403f

def z408 : W := mkw 0xc0c2633345dbe7ec 0x2e0613199a2edf3f 0x72862711cfffe7ff 0x7b9431388e7fff3f

def z409 : W := mkw 0x870217a12e835654 0x943810bd09741ab2 0x130607e18f8e0669 0x2898303f0c7c7033

def z410 : W := mkw 0x074040006b480000 0xa03a0200035a4000 0xe741c0007fc8000e 0x3f3a0e0003fe4000

def z411 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0x977fc0007f8e0008 0x2cbbfe0003fc7000

def z412 : W := mkw 0x0000804480000002 0x0000040224000000 0x000000ff80000001 0xc0000007fc000000

def z413 : W := mkw 0x00d0281a4050a988 0x08068140d202854c 0xa840381e4041f992 0xd54201c0f2020fcc

def z414 : W := mkw 0x0892bedd8000001f 0x004495f6ec000000 0xa941ffff80000001 0xfd4a0ffffc000000

def z415 : W := mkw 0x0fffbeddd060001f 0x407ffdf6ee830000 0xfffffffff0700007 0xffffffffff838000

def z416 : W := mkw 0x0fffbedfd060289f 0x487ffdf6fe830144 0xfffffffff0007801 0xffffffffff8003c0

def z417 : W := mkw 0x4000806480804222 0x0200040324040211 0x000000e180000661 0x000000070c000033

def z418 : W := mkw 0x070001202e815600 0x9038000901740ab0 0xe70000007f81fe1e 0x0f38000003fc0ff0

def z419 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x128607118c7e07e9 0x389430388c63f03f

def z420 : W := mkw 0x8002020100020044 0x0400101008001002 0x10060001800e0060 0x208030000c007003

def z421 : W := mkw 0x0835884c80000003 0x0041ac4264000000 0x0079c00e00000000 0x0003ce0070000000

def z422 : W := mkw 0x008222110000000c 0x0004111088000000 0x72862711804807fb 0x7b9431388c02403f

def z423 : W := mkw 0x8fb7bfdd8413855f 0x047dbdfeec209c2a 0xffffffff8c378005 0xfffffffffc61bc00

def z424 : W := mkw 0x006d4000516c0000 0x60036a00028b6000 0x0079c00000000000 0x0003ce0000000000

def z425 : W := mkw 0x0fffbffffef1ff9f 0xd87ffdfffff78ffc 0xfffffffffff1ff9f 0xffffffffffff8ffc

def z426 : W := mkw 0x0058080a50602880 0x4802c04052830144 0x0078000e00000000 0x0003c00070000000

def z427 : W := mkw 0x8002030104030444 0x0400101808201822 0x728607018c7e066f 0x3b9430380c63f033

def z428 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0x5fbfffe180000001 0x2afdffff0c000000

def z429 : W := mkw 0x8002030104030444 0x0400101808201822 0x0000070180000661 0x000000380c000033

def z430 : W := mkw 0x4090a87e8090ebaa 0x0a048543f404875d 0x080038ff8001fff1 0xc04001c7fc000fff

def z431 : W := mkw 0x0090281a0010a988 0x08048140d000854c 0xec00381e7001f996 0xc76001c0f3800fcc

def z432 : W := mkw 0xcff7ffffc5dbe7ff 0x2e7fbffffe2edf3f 0xffffffffcfffe7ff 0xfffffffffe7fff3f

def z433 : W := mkw 0x0725000000000000 0x0039280000000000 0x1307c00000000000 0x28983e0000000000

def z434 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0x4f003fe03f819e0d 0x0a7801ff01fc0cf0

def z435 : W := mkw 0x000000002a000000 0x8000000001500000 0x000000007f80000e 0x0000000003fc0000

def z436 : W := mkw 0x0892aa5d8000000f 0x00449552ec000000 0x0000001f80000000 0x00000000fc000000

def z437 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0x8d0018e07f81fe1e 0x846800c703fc0ff0

def z438 : W := mkw 0x476dc066fbec62a2 0xea3b6e0337df6315 0xf7ffc0ee7ffe600e 0xbfbffe0773fff300

def z439 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xa579c00073c8000a 0x3d2bce00039e4000

def z440 : W := mkw 0x0fb7befd8080421f 0x007dbdf7ec040210 0xffffffffc380661b 0xfffffffffe1c0330

def z441 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0x5effff1f80000000 0x32f7fff8fc000000

def z442 : W := mkw 0x476dc066fbec62a2 0xea3b6e0337df6315 0x8579c0ee73806000 0x842bce07739c0300

def z443 : W := mkw 0x07fd68187b6c0008 0xe03feb40c3db6000 0xfffff81e7ffe000e 0xffffffc0f3fff000

def z444 : W := mkw 0x004840007b6c0000 0xe002420003db6000 0xe4f800007ffe000e 0x1727c00003fff000

def z445 : W := mkw 0x0ffffeddd16c001f 0x607ffff6ee8b6000 0xffffffff807e0001 0xfffffffffc03f000

def z446 : W := mkw 0x00d8293a7ef1ff88 0xd806c149d3f78ffc 0xecf8381e7ff1ff9e 0xd767c1c0f3ff8ffc

def z447 : W := mkw 0x4ffffeffd1f8ebbf 0x6a7ffff7fe8fc75d 0xfffffffff3f9ffff 0xffffffffff9fcfff

def z448 : W := mkw 0x0000010004010400 0x0000000800200820 0x020007000c000609 0x0810003800600030

def z449 : W := mkw 0x0000000000000000 0x0000000000000000 0x6080000000700006 0x1304000000038000

def z450 : W := mkw 0x0000000000000000 0x0000000000000000 0x620000000c00000e 0x0b10000000600000

def z451 : W := mkw 0x8000010004138540 0x0400000800209c2a 0x200000118c7f87ff 0x790000008c63fc3f

def z452 : W := mkw 0x0000000000000000 0x0000000000000000 0xe4f8000000000000 0x1727c00000000000

def z453 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0x9dffd8ff80000000 0xb4effec7fc000000

def z454 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xf7ffc00073800000 0x3fbffe00039c0000

def z455 : W := mkw 0x000015a004815610 0x100000ad00240ab0 0xec003fe07001fe17 0xc76001ff03800ff0

def z456 : W := mkw 0xc0daeb7fd5fbefee 0x6e06d75bfeafdf7f 0xffffffffffffffff 0xffffffffffffffff

def z457 : W := mkw 0x406dc066d1ec62a2 0x6a036e03368f6315 0xb1ffc0ffc3fe67fb 0xfd8ffe07fe1ff33f

def z458 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0x95ffc00073fe0000 0x34affe00039ff000

def z459 : W := mkw 0x40d0e87ec1d8ebaa 0x2a068743f60ec75d 0xa941f8ffc3c9fffb 0xfd4a0fc7fe1e4fff

def z460 : W := mkw 0x4740d4e6ebc872b2 0xba3a06a7375e4395 0xad41d8fff3c87ffb 0xfd6a0ec7ff9e43ff

def z461 : W := mkw 0x8892bfdd8413855f 0x044495feec209c2a 0x7a863fff8c7f87ff 0xfbd431fffc63fc3f

def z462 : W := mkw 0x0f2797e5ae815617 0x90793cbf2d740ab0 0xff07ffe1ff81fe1f 0xeff83fff0ffc0ff0

def z463 : W := mkw 0x0f6fd6c5fb6c0017 0xe07b7eb62fdb6000 0xf7ffc7e1fffe000f 0x3fbffe3f0ffff000

def z464 : W := mkw 0x476dc046fb6c20a2 0xea3b6e0237db6105 0xf7ffc01ffffe01ee 0x3fbffe00fffff00f

def z465 : W := mkw 0x0f27d6c5ab0c0017 0xa0793eb62d586000 0x1307c7e18f8e0009 0x28983e3f0c7c7000

def z466 : W := mkw 0x00254000010c0000 0x20012a0000086000 0x1007c000000e0000 0x20803e0000007000

def z467 : W := mkw 0x076d00007a640000 0xc03b680003d32000 0xf6fe00007c760006 0x17b7f00003e3b000

def z468 : W := mkw 0x4040c046c14820a2 0x2a020602360a4105 0xa141c0ff804801e1 0xfd0a0e07fc02400f

def z469 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0x8cf8181e70707980 0x9467c0c0f38383cc

def z470 : W := mkw 0x476dc064fbec4222 0xe23b6e0327df6211 0xf7ffc0e1fffe066f 0x3fbffe070ffff033

def z471 : W := mkw 0x0058080a50602880 0x4802c04052830144 0xec78380e7001f816 0xc763c1c073800fc0

def z472 : W := mkw 0x40000022008062a0 0x0a00000110040315 0x00000000000067f0 0x000000000000033f

def z473 : W := mkw 0x004840007b6c0000 0xe002420003db6000 0x0000000073800000 0x00000000039c0000

def z474 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x108600118c7f87fe 0x308430008c63fc3f

def z475 : W := mkw 0x0fff3e9b5070a99d 0x487ff9f4da83854c 0xfefe3f1e7071f996 0xd7f7f1f8f3838fcc

def z476 : W := mkw 0x4040c046c14820a2 0x2a020602360a4105 0xa041c01fc04861f2 0xf5020e00fe02430f

def z477 : W := mkw 0x0ffffedffb7ca99f 0xe87ffff6ffdbe54c 0xfffffffffffff99f 0xffffffffffffffcc

def z478 : W := mkw 0x0f359ccc80000013 0x0079ace664000000 0xffffd8ee00000000 0xbffffec770000000

def z479 : W := mkw 0x00408046c0402082 0x0802040236020104 0xa141c0ffc0406193 0xfd0a0e07fe02030c

def z480 : W := mkw 0x4040402241c862a0 0x2a020201120e4315 0xa040001e43c867fa 0xd5020000f21e433f

def z481 : W := mkw 0x0000000000000000 0x0000000000000000 0x6200270000000001 0x4b10013800000000

def z482 : W := mkw 0x80da2a1b5072a9cc 0x4c06d150da83954e 0xfcfe381ff07ff9f6 0xf7e7f1c0ff83ffcf

def z483 : W := mkw 0x07a722110000000c 0x003d391088000000 0xf7ffe71180000001 0x7fbfff388c000000

def z484 : W := mkw 0x076dc044fb6c0002 0xe03b6e0227db6000 0xf7ffc0fffffe000f 0xffbffe07fffff000

def z485 : W := mkw 0x4892beff808062bf 0x0a4495f7fc040315 0x08003fff800067f1 0xc04001fffc00033f

def z486 : W := mkw 0x00c820125070a988 0x480641009283854c 0x608020107071f996 0x5304010083838fcc

def z487 : W := mkw 0x0fb7bedf8010a99f 0x087dbdf6fc00854c 0xffffffff8001f991 0xfffffffffc000fcc

def z488 : W := mkw 0x00c8201050708108 0x4006410082838408 0xe4f8201070718196 0x5727c10083838c0c

def z489 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xa141c0ee43c8600a 0xbd0a0e07721e4300

def z490 : W := mkw 0x0048400051680000 0x60024200028b4000 0xe5f9c00073f8000e 0x3f2fce00039fc000

def z491 : W := mkw 0x80c26311455b854c 0x240613188a2adc2a 0xf3c7e711cfff87ff 0x7f9e3f388e7ffc3f

def z492 : W := mkw 0x0000000000000000 0x0000000000000000 0xa10000e000000001 0xcd08000700000000

def z493 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0x4cf8381e30719984 0x1267c1c0f1838ccc

def z494 : W := mkw 0x0725000000000000 0x0039280000000000 0x8579c00000000000 0x042bce0000000000

def z495 : W := mkw 0x004840027b7ca980 0xe802420013dbe54c 0x000000007ffff99e 0x0000000003ffffcc

def z496 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0x8f001fe07f807e09 0x8c7800ff03fc03f0

def z497 : W := mkw 0x476dd5e6ffed76b2 0xfa3b6eaf37ff6bb5 0xffffffffffffffff 0xffffffffffffffff

def z498 : W := mkw 0x004800025070a980 0x480240001283854c 0x0000000000700180 0x000000000003800c

def z499 : W := mkw 0x002d000010240000 0x4001680000812000 0x10be000000360000 0x0085f0000001b000

def z500 : W := mkw 0x076d41207fed5600 0xf03b6a0903ff6ab0 0xf7ffc0007ffffe1e 0x3fbffe0003fffff0

def z501 : W := mkw 0x000000020010a980 0x080000001000854c 0x000000000001f990 0x0000000000000fcc

def z502 : W := mkw 0x0000000000108100 0x0000000000008408 0x0000000000718196 0x0000000000038c0c

def z503 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0x8141c0efc3886669 0xac0a0e077e1c4333

def z504 : W := mkw 0x07d83c9a5070a998 0x483ec1e4d283854c 0xeff83ffe7071f997 0xdf7fc1fff3838fcc

def z505 : W := mkw 0x0f2796c580000017 0x00793cb62c000000 0xff07ffe180000001 0xeff83fff0c000000

def z506 : W := mkw 0x076540006b4c0000 0xa03b2a00035a6000 0xb347c0004fce000a 0x3d9a3e00027e7000

def z507 : W := mkw 0x0025000000000000 0x0001280000000000 0x10ffc00000000000 0x3087fe0000000000

def z508 : W := mkw 0x006d4000516c0000 0x60036a00028b6000 0x72ffc0000c7e000e 0x3b97fe000063f000

def z509 : W := mkw 0xc0c2e377c5dbe7ee 0x2e06171bbe2edf3f 0xa141e7ffc3c9e7fb 0xfd0a0f3ffe1e4f3f

def z510 : W := mkw 0x072540002b0c0000 0xa0392a0001586000 0xf7ffc0000f8e0008 0x3fbffe00007c7000

def z511 : W := mkw 0x0000002000804200 0x0000000100040210 0x000000004380661a 0x00000000021c0330

def z512 : W := mkw 0x48d2feffc1c862bf 0x2a4697f7fe0e4315 0xa941ffffc3c867fb 0xfd4a0ffffe1e433f

def z513 : W := mkw 0x0080201000108108 0x0004010080008408 0x60802011807987ff 0x7b0401008c03cc3f

def z514 : W := mkw 0x077d480a7b6c2880 0xe83bea4053db6144 0xffffd80e7ffe780e 0xbffffec073fff3c0

def z515 : W := mkw 0x000015a004815610 0x100000ad00240ab0 0xa9003fe04381fe1b 0xcd4801ff021c0ff0

def z516 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0x56be00007ffe000e 0x02b5f00003fff000

def z517 : W := mkw 0x077d480a7b6c2880 0xe83bea4053db6144 0x8d79d80e73807800 0x846bcec0739c03c0

def z518 : W := mkw 0x0892bedf8010a99f 0x084495f6fc00854c 0x08003fff8001f991 0xc04001fffc000fcc

def z519 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xe4f8001e70700186 0x1727c000f383800c

def z520 : W := mkw 0x0000010004010400 0x0000000800200820 0x420027000c018004 0x0210013800600c00

def z521 : W := mkw 0x808222110012814c 0x040411108800940a 0x30860011807e07fb 0x798430008c03f03f

def z522 : W := mkw 0x08dabedfd070a99f 0x4846d5f6fe83854c 0xecf83ffff071f997 0xd767c1ffff838fcc

def z523 : W := mkw 0x008222110010810c 0x0004111088008408 0x7286271180718197 0x7b9431388c038c0c

def z524 : W := mkw 0x0048000050600000 0x4002400002830000 0xecf838007071f816 0xd767c1c003838fc0

def z525 : W := mkw 0x0700148000000010 0x003800a400000000 0xef003fe07001f817 0xcf7801ff03800fc0

def z526 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xef003fe00f800609 0xcf7801ff007c0030

def z527 : W := mkw 0x0fb7bfdd8401041f 0x007dbdfeec200820 0xffffffff8c01861f 0xfffffffffc600c30

def z528 : W := mkw 0x8fb7bfdd8413855f 0x047dbdfeec209c2a 0xffffffff800187f1 0xfffffffffc000c3f

def z529 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000000040006012 0xc500000002000300

def z530 : W := mkw 0x4700d5e4af895632 0xb23806af257c4ab1 0x0301c7e18f880669 0x28180e3f0c7c4033

def z531 : W := mkw 0x40c2e277c1c862ae 0x2a061713be0e4315 0xf3c7e7ffc3c867fb 0xff9e3f3ffe1e433f

def z532 : W := mkw 0x0080211004118508 0x0004010880208c28 0x628027100c71879f 0x5b14013880638c3c

def z533 : W := mkw 0x804801025473adc0 0x4c02400812a39d6e 0x000000007c7ffffe 0x0000000003e3ffff

def z534 : W := mkw 0x00d8281850708908 0x4006c140c2838448 0xecf8380070719806 0x1767c1c003838cc0

def z535 : W := mkw 0x074815a07ee15610 0xd03a40ad03f70ab0 0xeff83fe07ff1fe1f 0xdf7fc1ff03ff8ff0

def z536 : W := mkw 0x072540002b0c0000 0xa0392a0001586000 0x0101c00003800000 0x00080e00001c0000

def z537 : W := mkw 0x4f75dceec1c862b3 0x2a7baee7760e4315 0xad79d8ffc3c867fb 0xfd6bcec7fe1e433f

def z538 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0x000000ffc3c867fb 0xc0000007fe1e433f

def z539 : W := mkw 0x0ffdbcded070a99b 0x487fede6f683854c 0xedf9f8fe7071f996 0xd76fcfc7f3838fcc

def z540 : W := mkw 0x80ca63117f7f854c 0xe40653188bfbfc2a 0x72862711ffff87ff 0x7b9431388ffffc3f

def z541 : W := mkw 0x072500002a040000 0x8039280001502000 0x120600000c060000 0x0090300000603000

def z542 : W := mkw 0x0040000240402080 0x0802000012020104 0x8040000e40006000 0x8402000072000300

def z543 : W := mkw 0x4725c064ab8c4222 0xa2392e03255c6211 0x1307c0e18f8e0669 0x28983e070c7c7033

def z544 : W := mkw 0x0725804480000002 0x00392c0224000000 0xf7ffc0ff80000001 0xffbffe07fc000000

def z545 : W := mkw 0x070015802e011410 0x903800ac017008a0 0x020007000c000000 0x0010003800600000

def z546 : W := mkw 0x878237b12e93d75c 0x943c11bd89749eba 0x738627f18fff87ff 0x7b9c313f8c7ffc3f

def z547 : W := mkw 0x0000148000000010 0x000000a400000000 0x08003fe000000001 0xc04001ff00000000

def z548 : W := mkw 0x800001202e93d740 0x9400000901749eba 0x000000007ffffffe 0x0000000003ffffff

def z549 : W := mkw 0x8002030104030444 0x0400101808201822 0x720627018c0f867f 0x6b9031380c607c33

def z550 : W := mkw 0x4765c066c1c862a2 0x2a3b2e03360e4315 0xf7ffc0ffc3c867fb 0xffbffe07fe1e433f

def z551 : W := mkw 0x004840007b6c0000 0xe002420003db6000 0x728600007ffe000e 0x3b94300003fff000

def z552 : W := mkw 0x80d8291a5473adc8 0x4c06c148d2a39d6e 0xecf8381e7c7ffffe 0xd767c1c0f3e3ffff

def z553 : W := mkw 0x0018080810200800 0x4000c04040810040 0x0c38180030001800 0x0061c0c0018000c0

def z554 : W := mkw 0x07fd681a7b7ca988 0xe83feb40d3dbe54c 0xedf9f81e73f1f996 0xd76fcfc0f39f8fcc

def z555 : W := mkw 0x000000202a805200 0x9000000101540290 0x0000000073807800 0x00000000039c03c0

def z556 : W := mkw 0x870015a02e93d750 0x943800ad01749eba 0xef003fe07fffffff 0xcf7801ff03ffffff

def z557 : W := mkw 0x0000000000000000 0x0000000000000000 0x528600000c360004 0x029430000061b000

def z558 : W := mkw 0x070014a000804210 0x003800a500040210 0xef003fe04380661b 0xcf7801ff021c0330

def z559 : W := mkw 0x4765c066ebcc62a2 0xaa3b2e03375e6315 0xb347c0ffcfce67fb 0xfd9a3e07fe7e733f

def z560 : W := mkw 0x4048402251f8eba0 0x6a024201128fc75d 0x0000000073f9fffe 0x00000000039fcfff

def z561 : W := mkw 0x0ffffffdffed561f 0xf07fffffefff6ab0 0xfffffffffffffe1f 0xfffffffffffffff0

def z562 : W := mkw 0x0040402041c84200 0x20020201020e4210 0xa141c0e043c8661b 0xfd0a0e07021e4330

def z563 : W := mkw 0x8fffffddff7f855f 0xe47ffffeeffbfc2a 0xffffffffffff87ff 0xfffffffffffffc3f

def z564 : W := mkw 0x80da2b1b5473adcc 0x4c06d158daa39d6e 0xfefe3f1e7c77f996 0xd7f7f1f8f3e3bfcc

def z565 : W := mkw 0x8000010004138540 0x0400000800209c2a 0x620027000c7f87ff 0x4b1001380063fc3f

def z566 : W := mkw 0x404041226fc976a0 0xba020209137e4bb5 0x000000007fc9fffe 0x0000000003fe4fff

def z567 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0x0041c0ff804867f1 0xf0020e07fc02433f

def z568 : W := mkw 0x000001202e815600 0x9000000901740ab0 0xa10000e07f81fe1f 0xcd08000703fc0ff0

def z569 : W := mkw 0x0080201000000008 0x0004010080000000 0x6080201000000000 0x5304010080000000

def z570 : W := mkw 0x4040c046c14820a2 0x2a020602360a4105 0xa141c01fc3c801ea 0x3d0a0e00fe1e400f

def z571 : W := mkw 0x476d40227bec62a0 0xea3b6a0113df6315 0xf7ffc0007ffe67fe 0x3fbffe0003fff33f

def z572 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z573 : W := mkw 0x0700000000000000 0x0038000000000000 0xe700000000000000 0x0f38000000000000

def z574 : W := mkw 0x076d55a07fed5610 0xf03b6aad03ff6ab0 0xf7ffc7e07ffe060f 0x3fbffe3f03fff030

def z575 : W := mkw 0x076d4000516c0000 0x603b6a00028b6000 0xf7ffc000007e0000 0x3fbffe000003f000

def z576 : W := mkw 0x07fd281a5070a988 0x483fe940d283854c 0xfffff81e7071f996 0xffffffc0f3838fcc

def z577 : W := mkw 0x0098281810308908 0x4004c140c0818448 0xecf8381e30319804 0xd767c1c0f1818cc0

def z578 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xa141c0fe43c06192 0xd50a0e07f21e030c

def z579 : W := mkw 0x4048c066fbec62a2 0xea02460337df6315 0xa141c0fffffe67ff 0xfd0a0e07fffff33f

def z580 : W := mkw 0x40008066808062a2 0x0a00040334040315 0x200000ff804867fb 0xf9000007fc02433f

def z581 : W := mkw 0x0098281810308908 0x4004c140c0818448 0x00b8000000300000 0x0005c00000018000

def z582 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x528627118c7f81e4 0x329431388c63fc0f

def z583 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000180080669 0x280000000c004033

def z584 : W := mkw 0x0040000240402080 0x0802000012020104 0xec40381e7041f996 0xd76201c0f3820fcc

def z585 : W := mkw 0x400095e6848176b2 0x1a0004af34240bb5 0x08003fff8001fff1 0xc04001fffc000fff

def z586 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x528627000c7f87fe 0x029431380063fc3f

def z587 : W := mkw 0x0fb73fb92e81561d 0x907db9fdc9740ab0 0xffbe3fe07f81fe1f 0xcffdf1ff03fc0ff0

def z588 : W := mkw 0x4040c166efc976a2 0xba02060b377e4bb5 0xa141c0ffffc9ffff 0xfd0a0e07fffe4fff

def z589 : W := mkw 0x08ffaa5fd070a98f 0x4847fd52fe83854c 0xfcfff81ff071f996 0xf7e7ffc0ff838fcc

def z590 : W := mkw 0x878237912e13955c 0x943c11bc89709caa 0x5e863f003c379804 0x02f431f801e1bcc0

def z591 : W := mkw 0x0040000240402080 0x0802000012020104 0x0000000040406192 0x000000000202030c

def z592 : W := mkw 0x0000002000804200 0x0000000100040210 0xa10000f1c3c867fb 0xfd0800078e1e433f

def z593 : W := mkw 0x0002020100000004 0x0000101008000000 0x1206070180000001 0x289030380c000000

def z594 : W := mkw 0x8000000000128140 0x040000000000940a 0x00000000007e01e0 0x000000000003f00f

def z595 : W := mkw 0x0040400041480000 0x20020200020a4000 0xa141c011c3c807fb 0x7d0a0e008e1e403f

def z596 : W := mkw 0x878237b12e93d75c 0x943c11bd89749eba 0xff863fe07fb7fe1f 0xcffc31ff03fdbff0

def z597 : W := mkw 0x000001202e815600 0x9000000901740ab0 0xec0038007f81fe1e 0xc76001c003fc0ff0

def z598 : W := mkw 0x0892bffd8481561f 0x104495ffec240ab0 0x08003fff8001fe11 0xc04001fffc000ff0

def z599 : W := mkw 0x0008000010200000 0x4000400000810000 0x44b8000030300004 0x0225c00001818000

def z600 : W := mkw 0x0f27168100000015 0x007938b408000000 0x1206070000000000 0x0090303800000000

def z601 : W := mkw 0x4740d4e6ebc872b2 0xba3a06a7375e4395 0x8d41d8ee73807800 0x846a0ec7739c03c0

def z602 : W := mkw 0x4000c06481884222 0x22000603240c4211 0xa101c0e1c388667b 0xed080e070e1c4333

def z603 : W := mkw 0x072d15803e251410 0xd03968ac01f128a0 0x5ebe3f003c379804 0x02f5f1f801e1bcc0

def z604 : W := mkw 0x008222110000000c 0x0004111088000000 0x0000271180000001 0x400001388c000000

def z605 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xecf8381e00700180 0xd767c1c0f003800c

def z606 : W := mkw 0x0fb7bfddae01141f 0x907dbdfeed7008a0 0xffffffffbc019805 0xfffffffffde00cc0

def z607 : W := mkw 0x00fd681a517ca988 0x6807eb40d28be54c 0xfcfff81e707ff996 0xf7e7ffc0f383ffcc

def z608 : W := mkw 0x40008066808062a2 0x0a00040334040315 0xa10000ffc38067fb 0xcd080007fe1c033f

def z609 : W := mkw 0x0090281a0010a988 0x08048140d000854c 0x6880381e0071f996 0xd34401c0f0038fcc

def z610 : W := mkw 0x004840007b6c0000 0xe002420003db6000 0xa141c0007ffe000e 0x3d0a0e0003fff000

def z611 : W := mkw 0x0ff7bedfc040209f 0x087fbdf6fe020104 0xffffffffc0406193 0xfffffffffe02030c

def z612 : W := mkw 0x4040c166c5c966a2 0x2a02060b362e4b35 0xe341e7ffcfc9e7ff 0xff1a0f3ffe7e4f3f

def z613 : W := mkw 0x070000002a000000 0x8038000001500000 0x030000000f800008 0x08180000007c0000

def z614 : W := mkw 0x0000000000000000 0x0000000000000000 0xa141c00000000000 0x3d0a0e0000000000

def z615 : W := mkw 0x00c020124050a188 0x080601009202850c 0xe0c0201e4071e196 0xd7060100f2038f0c

def z616 : W := mkw 0xc002c365858b4666 0x2600161b2c2c5a33 0x1307c7e18f8e0669 0x28983e3f0c7c7033

def z617 : W := mkw 0x00fd681a517ca988 0x6807eb40d28be54c 0x10ffc01e007e0180 0x3087fe00f003f00c

def z618 : W := mkw 0x40408066c0c062a2 0x0a02040336060315 0xa04000ffc04067f3 0xd5020007fe02033f

def z619 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x728627118c378005 0x7b9431388c61bc00

def z620 : W := mkw 0x07fd681a7b7ca988 0xe83feb40d3dbe54c 0xf7ffc01e7ffe018e 0x3fbffe00f3fff00c

def z621 : W := mkw 0x808222110012814c 0x040411108800940a 0x72862711807e01e1 0x7b9431388c03f00f

def z622 : W := mkw 0x0fb73e990000001d 0x007db9f4c8000000 0xffbe3fe000000001 0xcffdf1ff00000000

def z623 : W := mkw 0x072d00003a240000 0xc039680001d12000 0x0438000030000000 0x0021c00001800000

def z624 : W := mkw 0x40008066808062a2 0x0a00040334040315 0x000000ee00006000 0x8000000770000300

def z625 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0x1b07ffff80000001 0xe8d83ffffc000000

def z626 : W := mkw 0x000014a000805210 0x100000a500040290 0x080018e000007800 0x804000c7000003c0

def z627 : W := mkw 0x87a723110413854c 0x043d391888209c2a 0xf7ffe7118c7f87ff 0x7fbfff388c63fc3f

def z628 : W := mkw 0x0098281810308908 0x4004c140c0818448 0x6cb8381030719996 0x5365c1c081838ccc

def z629 : W := mkw 0x076d41007f6d0400 0xe03b6a0803fb6820 0xf7ffe7007fff861f 0x7fbfff3803fffc30

def z630 : W := mkw 0x000015a004815610 0x100000ad00240ab0 0x6a003fe00c01fe1f 0xcb5001ff00600ff0

def z631 : W := mkw 0xc040c166c5dbe7e2 0x2e02060b362edf3f 0xa141c0ffcfffe7ff 0xfd0a0e07fe7fff3f

def z632 : W := mkw 0x0fb73e990000001d 0x007db9f4c8000000 0xfefe3f1e00000000 0xd7f7f1f8f0000000

def z633 : W := mkw 0x0048000050600000 0x4002400002830000 0xf6fe00007c7e000e 0x3fb7f00003e3f000

def z634 : W := mkw 0x0000000000000000 0x0000000000000000 0x200000000000061b 0x4900000000000030

def z635 : W := mkw 0x08b7aa5d8000000f 0x0045bd52ec000000 0x72ffe71f80000001 0x7b97ff38fc000000

def z636 : W := mkw 0x80922b1b0413adcc 0x0c049158d8209d6e 0x7a863f1f8c7fffff 0xfbd431f8fc63ffff

def z637 : W := mkw 0x0000000200002080 0x0800000010000104 0x0000001e00006190 0xc0000000f000030c

def z638 : W := mkw 0x40008066808062a2 0x0a00040334040315 0xa141c0ff800067f1 0xfd0a0e07fc00033f

def z639 : W := mkw 0x80ca23135473adcc 0x4c0651189aa39d6e 0x72862711fc7fffff 0x7b9431388fe3ffff

def z640 : W := mkw 0x07fd68187b7c8908 0xe03feb40c3dbe448 0xfffff8007fff980e 0x3fffffc003fffcc0

def z641 : W := mkw 0x074840007b6c0000 0xe03a420003db6000 0xe70000007ffe000e 0x0f38000003fff000

def z642 : W := mkw 0x0090281a0010a988 0x08048140d000854c 0x0000001e00000180 0x00000000f000000c

def z643 : W := mkw 0x08b7aa5d8000000f 0x0045bd52ec000000 0xb1ffc0ff80000001 0xfd8ffe07fc000000

def z644 : W := mkw 0x004800025070a980 0x480240001283854c 0xa040001e7071f996 0xd5020000f3838fcc

def z645 : W := mkw 0x0000804480000002 0x0000040224000000 0x8141c0ee00000000 0x840a0e0770000000

def z646 : W := mkw 0x0000000000000000 0x0000000000000000 0x080038000001f810 0xc04001c000000fc0

def z647 : W := mkw 0x0fb5bcdc8000001b 0x007dade6e4000000 0xedf9f8fe00000000 0xd76fcfc7f0000000

def z648 : W := mkw 0x808222110012814c 0x040411108800940a 0x1086000000360000 0x008430000001b000

def z649 : W := mkw 0x8892bfdd8413855f 0x044495feec209c2a 0x08003fff800187f1 0xc04001fffc000c3f

def z650 : W := mkw 0x0040002240c06280 0x0802000112060314 0xa14000fe43c0679b 0xdd0a0007f21e033c

def z651 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0x030007e07f81fe1f 0x0818003f03fc0ff0

def z652 : W := mkw 0x0000158004011410 0x100000ac002008a0 0x08003f0000019800 0x004001f800000cc0

def z653 : W := mkw 0x0000000000000000 0x0000000000000000 0x8c00180070007800 0x846000c0038003c0

def z654 : W := mkw 0x0f359decae815613 0x9079acef65740ab0 0xef79ffee7f81fe1f 0xcf7bcfff73fc0ff0

def z655 : W := mkw 0x08109ccc80000013 0x004084e664000000 0x080018ee00000000 0x804000c770000000

def z656 : W := mkw 0x00d8281850600008 0x4006c140c2830000 0xecf8381e70700006 0xd767c1c0f3838000

def z657 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000c7e000e 0x000000000063f000

def z658 : W := mkw 0x0fb73e990000001d 0x007db9f4c8000000 0xffffff0000000000 0x3ffffff800000000

def z659 : W := mkw 0x0ffffeddfb6c001f 0xe07ffff6efdb6000 0xfffffffff3800001 0xffffffffff9c0000

def z660 : W := mkw 0x00d8281a50602888 0x4806c140d2830144 0xecf8381e70007800 0xd767c1c0f38003c0

def z661 : W := mkw 0x8fffbfdfd473addf 0x4c7ffdfefea39d6e 0xfffffffffc7fffff 0xffffffffffe3ffff

def z662 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0x0041c01fc3c867fa 0x30020e00fe1e433f

def z663 : W := mkw 0x0000010004010400 0x0000000800200820 0x000000000c01861e 0x0000000000600c30

def z664 : W := mkw 0x0000000000000000 0x0000000000000000 0x200000000048000a 0x3900000000024000

def z665 : W := mkw 0x0082a2558000000e 0x00041512ac000000 0xf3c7e7ff80000001 0xff9e3f3ffc000000

def z666 : W := mkw 0x07983d983e319d18 0xd03cc1ecc1f18ce8 0x4eb83f003c319804 0x0275c1f801e18cc0

def z667 : W := mkw 0x4740c066ebc862a2 0xaa3a0603375e4315 0xe741c0ffffc867ff 0xff3a0e07fffe433f

def z668 : W := mkw 0x0000002000804200 0x0000000100040210 0x000000e000006611 0xc000000700000330

def z669 : W := mkw 0x000015a004815610 0x100000ad00240ab0 0x000007e000000601 0x0000003f00000030

def z670 : W := mkw 0x08ffea5dd16c000f 0x6047ff52ee8b6000 0x10ffc01f807e0000 0x3087fe00fc03f000

def z671 : W := mkw 0x0f92bffdae81561f 0x907c95ffed740ab0 0xef003fffff81fe1f 0xcf7801fffffc0ff0

def z672 : W := mkw 0x40d8683a51f8eba8 0x6a06c341d28fc75d 0xecf8381e73f9fffe 0xd767c1c0f39fcfff

def z673 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x120627118c0f87f9 0x689031388c607c3f

def z674 : W := mkw 0x87af23113e37854c 0xc43d791889f1bc2a 0x76be2711bc7f87ff 0x7bb5f1388de3fc3f

def z675 : W := mkw 0x87af23113e37854c 0xc43d791889f1bc2a 0x56be27003c378004 0x02b5f13801e1bc00

def z676 : W := mkw 0x8f2797c584030457 0x04793cbe2c201822 0x1307c7e18c0e0669 0x28983e3f0c607033

def z677 : W := mkw 0x008222110000000c 0x0004111088000000 0x1086001180000000 0x308430008c000000

def z678 : W := mkw 0x00d8a85ed070a98a 0x4806c542f683854c 0xedf9f8fff071f997 0xff6fcfc7ff838fcc

def z679 : W := mkw 0x078237b12e81561c 0x903c11bd89740ab0 0xff863ff1ff81fe1f 0xfffc31ff8ffc0ff0

def z680 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0x630027e00f81861f 0x4b18013f007c0c30

def z681 : W := mkw 0x0010080a00002880 0x0800804050000144 0x0800180e00007800 0x804000c0700003c0

def z682 : W := mkw 0x07d8281a7a70a988 0xc83ec140d3d3854c 0xeff8381e7ff1f99e 0xdf7fc1c0f3ff8fcc

def z683 : W := mkw 0x0010080800000000 0x0000804040000000 0x8c78180e00000000 0x8463c0c070000000

def z684 : W := mkw 0x070015802e011410 0x903800ac017008a0 0xee003f007c01f816 0xc77001f803e00fc0

def z685 : W := mkw 0x00d8681a7b7ca988 0xe806c340d3dbe54c 0xecf8381e7ffff99e 0xd767c1c0f3ffffcc

def z686 : W := mkw 0x47d8fdfefff9ffba 0xfa3ec7eff7ffcffd 0xeff9fffffff9ffff 0xff7fcfffffffcfff

def z687 : W := mkw 0x0000002000804200 0x0000000100040210 0xed0038e07381fe1f 0xcf6801c7039c0ff0

def z688 : W := mkw 0x076d55a07fed5610 0xf03b6aad03ff6ab0 0xef79ffe07f81fe1f 0xcf7bcfff03fc0ff0

def z689 : W := mkw 0x4740d5e6efc976b2 0xba3a06af377e4bb5 0xa341c7ffcfc867fb 0xfd1a0e3ffe7e433f

def z690 : W := mkw 0x4040402241c862a0 0x2a020201120e4315 0x20000011c3c867fb 0x790000008e1e433f

def z691 : W := mkw 0x0000804480000002 0x0000040224000000 0x0041c01f80000000 0x30020e00fc000000

def z692 : W := mkw 0x00484000516c0000 0x60024200028b6000 0x00000000007e0000 0x000000000003f000

def z693 : W := mkw 0x0765400041480000 0x203b2a00020a4000 0xf7ffc00043c8000a 0x3fbffe00021e4000

def z694 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000200000018016 0x4300010000000c00

def z695 : W := mkw 0x07903dba2e91ff98 0x983c81edd1748ffc 0xef003ffe7f81ff9f 0xcf7801fff3fc0ffc

def z696 : W := mkw 0x00d0281a40402088 0x08068140d2020104 0xecf8381e40406192 0xd767c1c0f202030c

def z697 : W := mkw 0x00922a190000000c 0x00049150c8000000 0xfefe3f1f80000001 0xfff7f1f8fc000000

def z698 : W := mkw 0x0700158004010410 0x003800ac00200820 0xef003fe00c01861f 0xcf7801ff00600c30

def z699 : W := mkw 0x4ff7feffc1c862bf 0x2a7fbff7fe0e4315 0xffffffffc3806001 0xfffffffffe1c0300

def z700 : W := mkw 0x0000000000000000 0x0000000000000000 0xe400000070000006 0x0720000003800000

def z701 : W := mkw 0x4000c04481080022 0x2200060224084001 0x0001c00180080060 0x20000e000c004003

def z702 : W := mkw 0x47fde87efbfcebaa 0xea3fef43f7dfe75d 0xfffff8ffffffffff 0xffffffc7ffffffff

def z703 : W := mkw 0x0f2796c580000017 0x00793cb62c000000 0xf7ffc7e180000001 0x3fbffe3f0c000000

def z704 : W := mkw 0x0040400041480000 0x20020200020a4000 0x0041c00000480000 0x30020e0000024000

def z705 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000011800007f1 0x400000008c00003f

def z706 : W := mkw 0x8002030104030444 0x0400101808201822 0x320607118c4e07fb 0x799030388c62703f

def z707 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xe541c0fff3c867ff 0xff2a0e07ff9e433f

def z708 : W := mkw 0x8002030104138544 0x0400101808209c2a 0x728607018c7f87ff 0x3b9430380c63fc3f

def z709 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0x0141c0ffc3c867fb 0x380a0e07fe1e433f

def z710 : W := mkw 0x006d40007b6c0000 0xe0036a0003db6000 0xf4ffc0007ffe000e 0x37a7fe0003fff000

def z711 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xccf8381e7071f984 0x9667c1c0f3838fcc

def z712 : W := mkw 0x878236b12a92d35c 0x943c11b58954969a 0x9d8618f1f3fe79e0 0xb4ec30c78f9ff3cf

def z713 : W := mkw 0xc0c2e377c5dbe7ee 0x2e06171bbe2edf3f 0xd3c7e7ee4fb7e004 0x869e3f3f727dbf00

def z714 : W := mkw 0x076d40027b6c2880 0xe83b6a0013db6144 0xf7ffc0007ffe780e 0x3fbffe0003fff3c0

def z715 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0x4cb8381e7071f996 0xc265c1c0f3838fcc

def z716 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xcf003fe07f81fe1e 0x867801ff03fc0ff0

def z717 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0x8141c0ffc3c867e9 0xbc0a0e07fe1e433f

def z718 : W := mkw 0x08b7bedd8000001f 0x0045bdf6ec000000 0xfcffffff80000001 0xf7e7fffffc000000

def z719 : W := mkw 0x805a0b0b54632cc4 0x4c02d0585aa31966 0x9e7e1f0ffc0e7e69 0xacf3f0f87fe073f3

def z720 : W := mkw 0x08b7bedd8000001f 0x0045bdf6ec000000 0xb9ffffff80000001 0xfdcffffffc000000

def z721 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xf7ffc0007fb6000e 0x0fbffe0003fdb000

def z722 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0x8d003fe07381f800 0x846801ff039c0fc0

def z723 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x128627118c7f87f9 0x789431388c63fc3f

def z724 : W := mkw 0x00d8281850600008 0x4006c140c2830000 0xecf8381e7071f816 0xd767c1c0f3838fc0

def z725 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0x57bfc0007ffe000e 0x2abdfe0003fff000

def z726 : W := mkw 0x072515a02e815610 0x903928ad01740ab0 0xffffffe07ffffe1f 0xffffffff03fffff0

def z727 : W := mkw 0x4740d5c6ef4934b2 0xba3a06ae377a49a5 0x4e41ff1fbc4999e4 0x32720ff8fde24ccf

def z728 : W := mkw 0x08dafeddfb6c001f 0xe046d7f6efdb6000 0x08003ffffffe000f 0xc04001fffffff000

def z729 : W := mkw 0x87ef63117f7f854c 0xe43f7b188bfbfc2a 0x8579e711f38187f1 0x442bcf388f9c0c3f

def z730 : W := mkw 0x4000c066818862a2 0x2a000603340c4315 0x2101c0ff83c867fb 0xf9080e07fc1e433f

def z731 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xfefe381e7071f996 0xfff7f1c0f3838fcc

def z732 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0x97ffc0007ffe0008 0x3cbffe0003fff000

def z733 : W := mkw 0x4048c066d1e86aa2 0x6a024603368f4355 0xa141c0fff3c87ffb 0xfd0a0e07ff9e43ff

def z734 : W := mkw 0x0f6f96c7d070a997 0x487b7cb63e83854c 0x1307c7e1f071f997 0x28983e3f0f838fcc

def z735 : W := mkw 0xc048412255fbefe0 0x6e02420912afdf7f 0x000000007ffffffe 0x0000000003ffffff

def z736 : W := mkw 0x0fb7bedd8010811f 0x007dbdf6ec008408 0xffffffff80318005 0xfffffffffc018c00

def z737 : W := mkw 0x8fbf3f993e37855d 0xc47df9fcc9f1bc2a 0x5ebe3f003c378004 0x02f5f1f801e1bc00

def z738 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xac78381e7041f992 0xd563c1c0f3820fcc

def z739 : W := mkw 0x0f27d7e5af8d5617 0xb0793ebf2d7c6ab0 0x1307c7e18f8e0609 0x28983e3f0c7c7030

def z740 : W := mkw 0x0058080a5070a980 0x4802c0405283854c 0xec78380e7071f996 0xc763c1c073838fcc

def z741 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xef003fe07381fe11 0xcf7801ff039c0ff0

def z742 : W := mkw 0x0048000250602080 0x4802400012830104 0xecf8381e7071f996 0xd767c1c0f3838fcc

def z743 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x528627118c7f87ed 0x3a9431388c63fc3f

def z744 : W := mkw 0x476dd4e6fbec72b2 0xfa3b6ea737df6395 0x8d79d8ee73807800 0x846bcec7739c03c0

def z745 : W := mkw 0x808223110413854c 0x0404111888209c2a 0xfe863f118c7f87ff 0xfff431f88c63fc3f

def z746 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xf7ffc0000ffe0008 0x3fbffe00007ff000

def z747 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0x8141c0ffc3c867fb 0xc40a0e07fe1e433f

def z748 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffee00000001 0xcfffffff70000000

def z749 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xeef83f1e7071f997 0xdf77c1f8f3838fcc

def z750 : W := mkw 0x4048c066d1e862a2 0x6a024603368f4315 0xf7ffc0fffffe67ff 0xffbffe07fffff33f

def z751 : W := mkw 0x08b7bedd8000001f 0x0045bdf6ec000000 0x7affffff80000001 0xfbd7fffffc000000

def z752 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xd7ffc0007ffe0004 0x36bffe0003fff000

def z753 : W := mkw 0x4ff77ebb41c862bd 0x2a7fbbf5da0e4315 0x5ebe3f0043c867fa 0x02f5f1f8021e433f

def z754 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xfffff8007ffe000e 0xffffffc003fff000

def z755 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xcf003fe07f81fe0d 0x8e7801ff03fc0ff0

def z756 : W := mkw 0x4000c066818862a2 0x2a000603340c4315 0xa101c0ffc38867fb 0xed080e07fe1c433f

def z757 : W := mkw 0x076d54807b6c1010 0xf03b6aa403db6080 0xffffd8007ffe180e 0x3ffffec003fff0c0

def z758 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xcf003fe07f81fe15 0xc67801ff03fc0ff0

def z759 : W := mkw 0x07a7a2558000000e 0x003d3d12ac000000 0xf7ffe7ff80000001 0xffbfff3ffc000000

def z760 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xecf8381e7071ff9f 0xdf67c1c0f3838ffc

def z761 : W := mkw 0x006d55a055ed5610 0x70036aad02af6ab0 0x18ffffe0007ffe11 0xf0c7ffff0003fff0

def z762 : W := mkw 0x0000806480804202 0x0000040324040210 0xa141c0ffc3c867fb 0xfd0a0e07fe1e433f

def z763 : W := mkw 0x0040c044c1480002 0x20020602260a4000 0xa141c0ffc3c807fb 0xfd0a0e07fe1e403f

def z764 : W := mkw 0x0f359ccc80000013 0x0079ace664000000 0xef79ffff80000001 0xff7bcffffc000000

def z765 : W := mkw 0x0098281a1030a988 0x4804c140d081854c 0x4cb8380e3031f804 0x8265c1c071818fc0

def z766 : W := mkw 0x4098e87c91b8cb2a 0x6204c743e48dc659 0x4db9f8e1b3b99e6d 0x2a6dcfc70d9dccf3

def z767 : W := mkw 0x80da2a1b5072a9cc 0x4c06d150da83954e 0xfcfe381e7077f996 0xd7e7f1c0f383bfcc

def z768 : W := mkw 0x0fb7beddaa00101f 0x907dbdf6ed500080 0xffffffffb0001801 0xfffffffffd8000c0

def z769 : W := mkw 0x0f379ecd80000017 0x0079bcf66c000000 0x137fc7ef80000001 0x289bfe3f7c000000

def z770 : W := mkw 0x80922b1904138d4c 0x04049158c8209c6a 0x7a863f118c7f9fff 0x7bd431f88c63fcff

def z771 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xedf9ffff80000001 0xd76fcffffc000000

def z772 : W := mkw 0x0f379ecd80000017 0x0079bcf66c000000 0xbf7fdfff80000001 0xfdfbfefffc000000

def z773 : W := mkw 0x8002030104138544 0x0400101808209c2a 0x320607118c7f87ff 0x799030388c63fc3f

def z774 : W := mkw 0x08b7ab7dae81560f 0x9045bd5bed740ab0 0x10ffc01fff81fe1e 0x3087fe00fffc0ff0

def z775 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xedf8381e73f1f99e 0xdf6fc1c0f39f8fcc

def z776 : W := mkw 0x80922b190413854c 0x04049158c8209c2a 0xfefe3f1ffc7fffff 0xfff7f1f8ffe3ffff

def z777 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xedf9f81e7071f996 0xff6fcfc0f3838fcc

def z778 : W := mkw 0x07d83dba7ef1ff98 0xd83ec1edd3f78ffc 0x03f807fe0ff00789 0x181fc03ff07f803c

def z779 : W := mkw 0x8f2797e5ae835657 0x94793cbf2d741ab2 0x1307c7e18f8e0669 0x28983e3f0c7c7033

def z780 : W := mkw 0x072515a02e815610 0x903928ad01740ab0 0xff07ffe07f81fe1f 0xeff83fff03fc0ff0

def z781 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0x8f003fe07f81fe19 0xcc7801ff03fc0ff0

def z782 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xef003ff07fc1ff9f 0xdf7801ff83fe0ffc

def z783 : W := mkw 0x00d8281a50602888 0x4806c140d2830144 0xecf8381e7001f816 0xd767c1c0f3800fc0

def z784 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xecf8381e7079fffe 0xd767c1c0f383cfff

def z785 : W := mkw 0x0892bedd8000001f 0x004495f6ec000000 0xedf9ffff80000001 0xff6fcffffc000000

def z786 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xad41d8fff3c87ffb 0xfd6a0ec7ff9e43ff

def z787 : W := mkw 0x0058080a50602880 0x4802c04052830144 0x8c78180e7001f816 0x8463c0c073800fc0

def z788 : W := mkw 0xc892bfff8493e7ff 0x0e4495fffc249f3f 0x08003fff8001e7f1 0xc04001fffc000f3f

def z789 : W := mkw 0x072515a02e815610 0x903928ad01740ab0 0xef79ffe07f81fe1f 0xcf7bcfff03fc0ff0

def z790 : W := mkw 0x004841227ffdff80 0xf802420913ffeffc 0x000000007fffff9e 0x0000000003fffffc

def z791 : W := mkw 0x472d8066baa462a2 0xca396c0335d52315 0x56be00ffbc3667f5 0xc2b5f007fde1b33f

def z792 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x7e863f11bc7f9fff 0x7bf431f88de3fcff

def z793 : W := mkw 0x808223110413854c 0x0404111888209c2a 0xf38627f18c7f87ff 0xff9c313f8c63fc3f

def z794 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0x8cf8181e7071f996 0x9467c0c0f3838fcc

def z795 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xef003fe1ff89fe7f 0xef7801ff0ffc4ff3

def z796 : W := mkw 0x00d8681a5178a988 0x6806c340d28bc54c 0xfffff81e7ffff99e 0xffffffc0f3ffffcc

def z797 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffff80080669 0xfffffffffc004033

def z798 : W := mkw 0x4f27d7e5af895637 0xb2793ebf2d7c4ab1 0x1307c7e18f880669 0x28983e3f0c7c4033

def z799 : W := mkw 0x4048c066d1e862a2 0x6a024603368f4315 0xa141c0fff3f867ff 0xfd0a0e07ff9fc33f

def z800 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0x9f7fffff80000001 0xecfbfffffc000000

def z801 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0x56ffc0007ffe000e 0x32b7fe0003fff000

def z802 : W := mkw 0x0fb7bedd8010811f 0x007dbdf6ec008408 0xffffffff8c7f819f 0xfffffffffc63fc0c

def z803 : W := mkw 0x48ffea5fd178a9af 0x6a47ff52fe8bc54d 0x10ffc01f807801e0 0x3087fe00fc03c00f

def z804 : W := mkw 0x00da2a1b5070a98c 0x4806d150da83854c 0xfefe3f1e7071f996 0xd7f7f1f8f3838fcc

def z805 : W := mkw 0x80da2a1b5072a9cc 0x4c06d150da83954e 0xfefe381ffc7ff9fe 0xfff7f1c0ffe3ffcf

def z806 : W := mkw 0x00d8681a517ca988 0x6806c340d28be54c 0xecf8381e707ff996 0xd767c1c0f383ffcc

def z807 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xef41ffe07f81fe1f 0xff7a0fff03fc0ff0

def z808 : W := mkw 0x076d54807b6c0010 0xe03b6aa403db6000 0xffffffe07ffff81f 0xffffffff03ffffc0

def z809 : W := mkw 0x00d8681a5178a988 0x6806c340d28bc54c 0xedf9f81ff3f9ffff 0xff6fcfc0ff9fcfff

def z810 : W := mkw 0x072594c480000012 0x00392ca624000000 0xffffffff80000001 0xfffffffffc000000

def z811 : W := mkw 0x404841227fed76a0 0xfa02420913ff6bb5 0x000000007ffffffe 0x0000000003ffffff

def z812 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xecf8381e7031f804 0xd767c1c0f3818fc0

def z813 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xf7ffc0007fb60004 0x3fbffe0003fdb000

def z814 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xf7ffc0007ffe601e 0xffbffe0003fff300

def z815 : W := mkw 0x0058080a5070a980 0x4802c0405283854c 0x8c78180e7031f804 0x8463c0c073818fc0

def z816 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xf7ffc0007ffff81e 0x3fbffe0003ffffc0

def z817 : W := mkw 0xc092ab7f8493efee 0x0e04955bfc249f7f 0x08003fff8001fff1 0xc04001fffc000fff

def z818 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0x8141c0ffc3c867f1 0xf40a0e07fe1e433f

def z819 : W := mkw 0x0f359ccc80000013 0x0079ace664000000 0x8d79ffee00000001 0xc46bcfff70000000

def z820 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xa141c0ffcffe67ff 0xfd0a0e07fe7ff33f

def z821 : W := mkw 0x0fb7bedd8010811f 0x007dbdf6ec008408 0xffffffff80700181 0xfffffffffc03800c

def z822 : W := mkw 0x0000012004814600 0x0000000900240a30 0xef003fe07f81fe1f 0xcf7801ff03fc0ff0

def z823 : W := mkw 0x8002030104138544 0x0400101808209c2a 0x120607018c7e07e9 0x289030380c63f03f

def z824 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xa941f8ffc3c9fffb 0xfd4a0fc7fe1e4fff

def z825 : W := mkw 0x4048c066d1e862a2 0x6a024603368f4315 0xa579c0fff3c867fb 0xfd2bce07ff9e433f

def z826 : W := mkw 0x006d40007b6c0000 0xe0036a0003db6000 0xb1ffc0007ffe000e 0x3d8ffe0003fff000

def z827 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xfffffffff0000007 0xffffffffff800000

def z828 : W := mkw 0x8fb7bedd8002005f 0x047dbdf6ec001002 0xffffffff800e0061 0xfffffffffc007003

def z829 : W := mkw 0x40008066808062a2 0x0a00040334040315 0xa141c0ffc38067fb 0xfd0a0e07fe1c033f

def z830 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0x4cf8381e7071f996 0x1267c1c0f3838fcc

def z831 : W := mkw 0x404841227ff9ffa0 0xfa02420913ffcffd 0x000000007ff9fffe 0x0000000003ffcfff

def z832 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffffc380000b 0xfffffffffe1c0000

def z833 : W := mkw 0x8f359dcc84138553 0x0479acee64209c2a 0x8d79d8ee0c7f87fe 0x846bcec77063fc3f

def z834 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xa141c0ffc3c807eb 0x3d0a0e07fe1e403f

def z835 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xe1c1c0ffc3f867ff 0xff0e0e07fe1fc33f

def z836 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffff8048000b 0xfffffffffc024000

def z837 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xff863ff1ffffffff 0xfffc31ff8fffffff

def z838 : W := mkw 0x00d0281a40402088 0x08068140d2020104 0xecf8381e7041f996 0xd767c1c0f3820fcc

def z839 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xfefe381ffc7fffff 0xfff7f1c0ffe3ffff

def z840 : W := mkw 0x870015a02e835650 0x943800ad01741ab2 0xef003fe07f8ffe7f 0xcf7801ff03fc7ff3

def z841 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0x9dffffff80000001 0xf4effffffc000000

def z842 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xccf8381e7031f994 0xc667c1c0f3818fcc

def z843 : W := mkw 0x072500002a000000 0x8039280001500000 0xf7ffc0007ffe000e 0x3fbffe0003fff000

def z844 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0x8d79ffee00000000 0x846bcfff70000000

def z845 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xfffffffe00000000 0xd7fffffff0000000

def z846 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x72862711fc7fffff 0x7b9431388fe3ffff

def z847 : W := mkw 0x000015a02e815610 0x900000ad01740ab0 0xa9003fe07f81fe1f 0xcd4801ff03fc0ff0

def z848 : W := mkw 0x072d40003b2c0000 0xe0396a0001d96000 0x77bfc0003ffe000e 0x3bbdfe0001fff000

def z849 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xfcfe381e707ff996 0xf7e7f1c0f383ffcc

def z850 : W := mkw 0x8892bffd8493d75f 0x144495ffec249eba 0x08003fff8001fff1 0xc04001fffc000fff

def z851 : W := mkw 0x0f379ecd80000017 0x0079bcf66c000000 0x8d79dfef80000001 0x846bceff7c000000

def z852 : W := mkw 0x0790bcdc8000001a 0x003c85e6e4000000 0xeff9ffff80000001 0xff7fcffffc000000

def z853 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x120627118c7f87ff 0x689031388c63fc3f

def z854 : W := mkw 0x0fb7beddaa00001f 0x807dbdf6ed500000 0xfffffffff3800001 0xffffffffff9c0000

def z855 : W := mkw 0x076d40027b6c2080 0xe83b6a0013db6104 0xf7ffc0007ffe619e 0x3fbffe0003fff30c

def z856 : W := mkw 0x006d40007b6c0000 0xe0036a0003db6000 0x72ffc0007ffe000e 0x3b97fe0003fff000

def z857 : W := mkw 0xc04841227fffe7e0 0xee02420913ffff3f 0x000000007fffe7fe 0x0000000003ffff3f

def z858 : W := mkw 0x4048c066d1e862a2 0x6a024603368f4315 0xedf9f8fff3f9ffff 0xff6fcfc7ff9fcfff

def z859 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xef003fe07fc9ffff 0xcf7801ff03fe4fff

def z860 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xe5f9c0ffc3c867fb 0xff2fce07fe1e433f

def z861 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0x8141c0ffc3c867fa 0xb40a0e07fe1e433f

def z862 : W := mkw 0x0fb7bedd8010811f 0x007dbdf6ec008408 0xffffffff807987ff 0xfffffffffc03cc3f

def z863 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xf7ffc011fffe000f 0x7fbffe008ffff000

def z864 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0x57ffc0003ffe000c 0x3abffe0001fff000

def z865 : W := mkw 0x07b5681a2b1ca988 0xa83dab40d158e54c 0x1b07f81e0f8ff998 0xe8d83fc0f07c7fcc

def z866 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xef403ffe7f81fe1f 0xdf7a01fff3fc0ff0

def z867 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0x5effffff80000001 0xf2f7fffffc000000

def z868 : W := mkw 0x076d54807b6c0010 0xe03b6aa403db6000 0xf7ffc7e07ffe000f 0x3fbffe3f03fff000

def z869 : W := mkw 0x000015a02e815610 0x900000ad01740ab0 0x6a003fe07f81fe1f 0xcb5001ff03fc0ff0

def z870 : W := mkw 0x0f359ccc80000013 0x0079ace664000000 0xffffffee00000001 0xffffffff70000000

def z871 : W := mkw 0x4048c066d1ec62a2 0x6a024603368f6315 0xa141c0ffc3fe67fb 0xfd0a0e07fe1ff33f

def z872 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xf7ffe0007fff801e 0x7fbfff0003fffc00

def z873 : W := mkw 0x0f359ccc80000013 0x0079ace664000000 0x8f79dfee00000001 0x8c7bceff70000000

def z874 : W := mkw 0x0fb7beddaa00001f 0x807dbdf6ed500000 0xffffffffff81f81f 0xfffffffffffc0fc0

def z875 : W := mkw 0x80da2a1b5072a9cc 0x4c06d150da83954e 0xfcfe381ff07fffff 0xffe7f1c0ff83ffff

def z876 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xdfffffff80000001 0xc6fffffffc000000

def z877 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffffc0006013 0xfffffffffe000300

def z878 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xb3ffc7ff80000001 0xfd9ffe3ffc000000

def z879 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xfffffffff0007801 0xffffffffff8003c0

def z880 : W := mkw 0x072d40003b2c0000 0xe0396a0001d96000 0xf7ffc0003fbe000c 0x3fbffe0001fdf000

def z881 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0x4cf8381e3071f994 0xd267c1c0f1838fcc

def z882 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xff863fe07fb7fe1f 0xcffc31ff03fdbff0

def z883 : W := mkw 0x0010080800000000 0x0000804040000000 0xec78380e7001f816 0xc763c1c073800fc0

def z884 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffff8c360005 0xfffffffffc61b000

def z885 : W := mkw 0x006d4000516c0000 0x60036a00028b6000 0xf3ffc0004ffe000e 0x3f9ffe00027ff000

def z886 : W := mkw 0x8fb7bedd8012815f 0x047dbdf6ec00940a 0xffffffff807e07fb 0xfffffffffc03f03f

def z887 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x528627018c7f87ff 0x2a9431380c63fc3f

def z888 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xef003ff1ff81ffff 0xcf7801ff8ffc0fff

def z889 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffee00000000 0xbfffffff70000000

def z890 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0x9fffdfff80000001 0xbcfffefffc000000

def z891 : W := mkw 0x808223110413854c 0x0404111888209c2a 0xf3c7e7118c7f87ff 0x7f9e3f388c63fc3f

def z892 : W := mkw 0x00d8681a5178a988 0x6806c340d28bc54c 0xecf9f81e7079f996 0xf767cfc0f383cfcc

def z893 : W := mkw 0x072d40003b2c0000 0xe0396a0001d96000 0x13bfc0000fbe0008 0x289dfe00007df000

def z894 : W := mkw 0x0058080a50602880 0x4802c04052830144 0xec78381e7041f996 0xd763c1c0f3820fcc

def z895 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xb1c7c0ffc3fe67fb 0xfd8e3e07fe1ff33f

def z896 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x528627118c7f87ff 0x429431388c63fc3f

def z897 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x7a863f118c7fffff 0xfbd431f88c63ffff

def z898 : W := mkw 0x0f379ecd80000017 0x0079bcf66c000000 0xffffdfef80000001 0xbffffeff7c000000

def z899 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xf7ffc0107ffe019e 0x7fbffe0083fff00c

def z900 : W := mkw 0x070014802a000010 0x803800a401500000 0xef003fe07f81f81f 0xcf7801ff03fc0fc0

def z901 : W := mkw 0x076d40027b6c2080 0xe83b6a0013db6104 0xf7ffc01ffffe67ff 0xffbffe00fffff33f

def z902 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xff863fe07f81fe1f 0xfffc31ff03fc0ff0

def z903 : W := mkw 0x00da2a1b5070a98c 0x4806d150da83854c 0xecf83f1ff071f997 0xd767c1f8ff838fcc

def z904 : W := mkw 0x0092aa5d8000000e 0x00049552ec000000 0xffffffff80000001 0xfffffffffc000000

def z905 : W := mkw 0x0098281a1030a988 0x4804c140d081854c 0xecb8381e7031f996 0xc765c1c0f3818fcc

def z906 : W := mkw 0x0058080a5070a980 0x4802c0405283854c 0xac78181e7071f996 0xd563c0c0f3838fcc

def z907 : W := mkw 0x4000c066818862a2 0x2a000603340c4315 0x0101c0ff838807e9 0x28080e07fc1c403f

def z908 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xb3ffc0004ffe000a 0x3d9ffe00027ff000

def z909 : W := mkw 0x0fb7bedd8010891f 0x007dbdf6ec008448 0xffffffff80019801 0xfffffffffc000cc0

def z910 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffff800007f1 0xfffffffffc00003f

def z911 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xf7ffe7007ffe000f 0x7fbfff3803fff000

def z912 : W := mkw 0x0f359ccc80000013 0x0079ace664000000 0xcf79ffee00000000 0x867bcfff70000000

def z913 : W := mkw 0x0058080a50602880 0x4802c04052830144 0xecf8380e7071f816 0xd767c1c073838fc0

def z914 : W := mkw 0x8002030104030444 0x0400101808201822 0x728607118c7e07ff 0x7b9430388c63f03f

def z915 : W := mkw 0x0f379ecd80000017 0x0079bcf66c000000 0x9f7fdfee00000000 0x84fbfeff70000000

def z916 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffff8001f811 0xfffffffffc000fc0

def z917 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0x4e003fe07f81fe1f 0xc27001ff03fc0ff0

def z918 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x328607118c7e07fb 0x799430388c63f03f

def z919 : W := mkw 0x80da2a1b5072a9cc 0x4c06d150da83954e 0xecf8381ff071f9f6 0xd767c1c0ff838fcf

def z920 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xed003fe07381fe17 0xc76801ff039c0ff0

def z921 : W := mkw 0x07b53c9800000018 0x003da9e4c0000000 0xfffffffe00000001 0xfffffffff0000000

def z922 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xedf838fe7071f997 0xdf6fc1c7f3838fcc

def z923 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xef003fe07ffffe1f 0xcf7801ff03fffff0

def z924 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xecf8381ff071f997 0xff67c1c0ff838fcc

def z925 : W := mkw 0x0098281810308908 0x4004c140c0818448 0xecf8381e7031f816 0xd767c1c0f3818fc0

def z926 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xf7ffc0007ffe061f 0x7fbffe0003fff030

def z927 : W := mkw 0x0058080a5070a980 0x4802c0405283854c 0xecf8180e7071f996 0x9767c0c073838fcc

def z928 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xdfffffef80000001 0xaeffffff7c000000

def z929 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x728607118c7e07ef 0x3b9430388c63f03f

def z930 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xff063fe07f8ffe1f 0xeff831ff03fc7ff0

def z931 : W := mkw 0x4048c066d1e862a2 0x6a024603368f4315 0xa1f9c0ffc3f867fb 0xfd0fce07fe1fc33f

def z932 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0x0b003fe07f81fe1f 0xc85801ff03fc0ff0

def z933 : W := mkw 0x0fb7beddaa00001f 0x807dbdf6ed500000 0xfffffffffffe000f 0xfffffffffffff000

def z934 : W := mkw 0x008222110000000c 0x0004111088000000 0x728627118c7e07ff 0x7b9431388c63f03f

def z935 : W := mkw 0x80922b190413854c 0x04049158c8209c2a 0x72fe271f8c7f87ff 0x7b97f138fc63fc3f

def z936 : W := mkw 0x076d54807b6c0010 0xe03b6aa403db6000 0xffffff007ffe000e 0x3ffffff803fff000

def z937 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xe341e7ffc3c867fb 0xff1a0f3ffe1e433f

def z938 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xa141c0fff3c9ffff 0xfd0a0e07ff9e4fff

def z939 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffff80400193 0xfffffffffc02000c

def z940 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xf7ffc011fffe01ee 0x3fbffe008ffff00f

def z941 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xa141c0ffc3c067f3 0xd50a0e07fe1e033f

def z942 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0x0141c0ff83c867f9 0xf80a0e07fc1e433f

def z943 : W := mkw 0x8fb7bedd8012815f 0x047dbdf6ec00940a 0xffffffff80360001 0xfffffffffc01b000

def z944 : W := mkw 0x0f2796c580000017 0x00793cb62c000000 0xf7ffc7ff80000001 0xffbffe3ffc000000

def z945 : W := mkw 0x0fb7beddaa04001f 0x807dbdf6ed502000 0xffffffff8c060001 0xfffffffffc603000

def z946 : W := mkw 0x808223110413854c 0x0404111888209c2a 0xf6862711fc7f87ff 0x7fb431388fe3fc3f

def z947 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xad003fe07381fe1b 0xcd6801ff039c0ff0

def z948 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xeef8381e7c71f99e 0xdf77c1c0f3e38fcc

def z949 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0x95ffc0007ffe000e 0x34affe0003fff000

def z950 : W := mkw 0x076d40027b6c2080 0xe83b6a0013db6104 0xfffff81e7ffff99e 0xffffffc0f3ffffcc

def z951 : W := mkw 0x0098281a1030a988 0x4804c140d081854c 0x6cb8381e3071f996 0xd365c1c0f1838fcc

def z952 : W := mkw 0x40d8681a5178a9a8 0x6a06c340d28bc54d 0xecf8381e7079f9f6 0xd767c1c0f383cfcf

def z953 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0x1bffffff80000001 0xf8dffffffc000000

def z954 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0x73ffe7ff80000001 0x7b9fff3ffc000000

def z955 : W := mkw 0x80d8281a5072a9c8 0x4c06c140d283954e 0xecf8381e707ff9f6 0xd767c1c0f383ffcf

def z956 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffffb0019805 0xfffffffffd800cc0

def z957 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffff80018017 0xfffffffffc000c00

def z958 : W := mkw 0x8fb7bedd8012815f 0x047dbdf6ec00940a 0xffffffff8c7e01ef 0xfffffffffc63f00f

def z959 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xed41f8ffc3c867fb 0xff6a0fc7fe1e433f

def z960 : W := mkw 0x08ffea5fd17ca98f 0x6847ff52fe8be54c 0x10ffc01f807e0180 0x3087fe00fc03f00c

def z961 : W := mkw 0x0058080a50602880 0x4802c04052830144 0x8c78380e7001f810 0xc463c1c073800fc0

def z962 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0x8c78381e7071f996 0xc463c1c0f3838fcc

def z963 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0x8d003fe07f81fe1f 0xc46801ff03fc0ff0

def z964 : W := mkw 0x4725d5e4af8d5632 0xb2392eaf257c6ab1 0x1307c7e18f8e0669 0x28983e3f0c7c7033

def z965 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xecf8380e7071f806 0x9767c1c073838fc0

def z966 : W := mkw 0x4f7ddceefbec62b3 0xea7beee777df6315 0x8d79d8ee73806000 0x846bcec7739c0300

def z967 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0x8141c0ffc38867f9 0xec0a0e07fe1c433f

def z968 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0x8cf8381e7071f990 0xd467c1c0f3838fcc

def z969 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xecf8381e7c7ff99e 0xd767c1c0f3e3ffcc

def z970 : W := mkw 0xc0daea5fd17aa9ee 0x6e06d752fe8bd54f 0x10ffc01f807e01e0 0x3087fe00fc03f00f

def z971 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xec78381e7001f996 0xc763c1c0f3800fcc

def z972 : W := mkw 0x072540002b0c0000 0xa0392a0001586000 0xf7ffc0000ffe000e 0x3fbffe00007ff000

def z973 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xf7ffc01e7ffe000e 0xffbffe00f3fff000

def z974 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xf7ffc001fffe066f 0x3fbffe000ffff033

def z975 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xecf8381e7001f990 0xd767c1c0f3800fcc

def z976 : W := mkw 0x8fb73f992e13955d 0x947db9fcc9709caa 0x5ebe3f003c379804 0x02f5f1f801e1bcc0

def z977 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x128607118c7f87ff 0x389430388c63fc3f

def z978 : W := mkw 0x0058080a5070a980 0x4802c0405283854c 0x8c78180e7001f990 0x8463c0c073800fcc

def z979 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x528627118c7f87fe 0x329431388c63fc3f

def z980 : W := mkw 0x000015a02e815610 0x900000ad01740ab0 0x08003fe07381fe11 0xc04001ff039c0ff0

def z981 : W := mkw 0x8fb7bedd8012815f 0x047dbdf6ec00940a 0xffffffff800001e1 0xfffffffffc00000f

def z982 : W := mkw 0x00da2a1b5070a98c 0x4806d150da83854c 0xfcfe381ff071f996 0xf7e7f1c0ff838fcc

def z983 : W := mkw 0x072515a02e815610 0x903928ad01740ab0 0xffbe3fe07f81fe1f 0xcffdf1ff03fc0ff0

def z984 : W := mkw 0x00da2a1b5070a98c 0x4806d150da83854c 0xfefe3f1ff079ffff 0xfff7f1f8ff83cfff

def z985 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xb347c0ffcfce67fb 0xfd9a3e07fe7e733f

def z986 : W := mkw 0x0090281800108108 0x00048140c0008408 0xecf8381e7071f996 0xd767c1c0f3838fcc

def z987 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xecf8380e7031f816 0xc767c1c073818fc0

def z988 : W := mkw 0x00d8681a5178a988 0x6806c340d28bc54c 0xedf9f81e73f1f996 0xd76fcfc0f39f8fcc

def z989 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xef003ff1ff81fe1f 0xff7801ff8ffc0ff0

def z990 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xccf8380e7071f996 0x8667c1c073838fcc

def z991 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xf7ffc7ff80000001 0x3fbffe3ffc000000

def z992 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xef803fe07ff1fe1f 0xdf7c01ff03ff8ff0

def z993 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0x4f003fe07f81fe1f 0x0a7801ff03fc0ff0

def z994 : W := mkw 0x006d40007b6c0000 0xe0036a0003db6000 0x10ffc0000ffe0008 0x3087fe00007ff000

def z995 : W := mkw 0x0048400051680000 0x60024200028b4000 0xf7ffc0007ffe000e 0x3fbffe0003fff000

def z996 : W := mkw 0x00d8681a5178a988 0x6806c340d28bc54c 0xecf8381e73f9f99e 0xd767c1c0f39fcfcc

def z997 : W := mkw 0x000015a004815610 0x100000ad00240ab0 0xed003fe07381fe1f 0xcf6801ff039c0ff0

def z998 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0x0101c0ffc3c867fb 0xe8080e07fe1e433f

def z999 : W := mkw 0x0098281a1030a988 0x4804c140d081854c 0x0c38381e3001f990 0xc061c1c0f1800fcc

def z1000 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xf3c7c0ffc3c867fb 0xff9e3e07fe1e433f

def z1001 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xa141c0ffc38067fb 0xcd0a0e07fe1c033f

def z1002 : W := mkw 0x476d40027b6c20a0 0xea3b6a0013db6105 0xf7ffc0007ffe01ee 0x3fbffe0003fff00f

def z1003 : W := mkw 0x070014a02a805210 0x903800a501540290 0xef003fe07381f817 0xcf7801ff039c0fc0

def z1004 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xef79ffff80000001 0xcf7bcffffc000000

def z1005 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffff8c7e07ff 0xfffffffffc63f03f

def z1006 : W := mkw 0x000015a02e815610 0x900000ad01740ab0 0xec003fe07f81fe1f 0xc76001ff03fc0ff0

def z1007 : W := mkw 0x070014a000804210 0x003800a500040210 0xef003fe07381fe1f 0xcf7801ff039c0ff0

def z1008 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffff8c00000f 0xfffffffffc600000

def z1009 : W := mkw 0x072d00003a240000 0xc039680001d12000 0xf7ffc0007fb6000e 0x3fbffe0003fdb000

def z1010 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xef003fe07f81f80e 0x8f7801ff03fc0fc0

def z1011 : W := mkw 0x076d40027b6c2080 0xe83b6a0013db6104 0xf7ffc01e7ffe018e 0x3fbffe00f3fff00c

def z1012 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xeff83fe07f81fe1f 0xdf7fc1ff03fc0ff0

def z1013 : W := mkw 0x808223110413854c 0x0404111888209c2a 0xf2c6271f8c7f87ff 0xff963138fc63fc3f

def z1014 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xef003fe07f81f816 0xc77801ff03fc0fc0

def z1015 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xe341c0ffcfc867ff 0xff1a0e07fe7e433f

def z1016 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0x8c78380e7001f800 0x8463c1c073800fc0

def z1017 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffff8c0e0009 0xfffffffffc607000

def z1018 : W := mkw 0x076d40027b6c2080 0xe83b6a0013db6104 0xf7ffc00e7ffe600e 0xbfbffe0073fff300

def z1019 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xfefe381e7c77f996 0xd7f7f1c0f3e3bfcc

def z1020 : W := mkw 0x0765400041480000 0x203b2a00020a4000 0xf7ffc0004ffe000e 0x3fbffe00027ff000

def z1021 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xf7ffc0007ffe07fe 0x3fbffe0003fff03f

def z1022 : W := mkw 0x072d40003b2c0000 0xe0396a0001d96000 0xf7bfc0007fbe000e 0x2fbdfe0003fdf000

def z1023 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x528627118c7f87f5 0x729431388c63fc3f

def z1024 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xfffff8007fff980e 0x3fffffc003fffcc0

def z1025 : W := mkw 0x4000c066818862a2 0x2a000603340c4315 0x0101c0ff838067f1 0xc0080e07fc1c033f

def z1026 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xe141e0ffc3c9e7ff 0xff0a0f07fe1e4f3f

def z1027 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0x13ffc0007ffe000e 0x389ffe0003fff000

def z1028 : W := mkw 0x0fb7beddaa00001f 0x807dbdf6ed500000 0xffffffffbc000005 0xfffffffffde00000

def z1029 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xdfffffff80000000 0xb6fffffffc000000

def z1030 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xecf8381ff071fff7 0xd767c1c0ff838fff

def z1031 : W := mkw 0x0fb7beddaa00001f 0x807dbdf6ed500000 0xffffffff8f800009 0xfffffffffc7c0000

def z1032 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffff804801e1 0xfffffffffc02400f

def z1033 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xd7ffc0007ffe000e 0x06bffe0003fff000

def z1034 : W := mkw 0x4000c06481884222 0x22000603240c4211 0xa141c0ff83c807fb 0xfd0a0e07fc1e403f

def z1035 : W := mkw 0x0fb7bedd8010811f 0x007dbdf6ec008408 0xfffffffff071f997 0xffffffffff838fcc

def z1036 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0x73ffc0000ffe000e 0x3b9ffe00007ff000

def z1037 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xd7ffc0007fbe000c 0x2ebffe0003fdf000

def z1038 : W := mkw 0x0090281a0010a988 0x08048140d000854c 0xecf8381e7001f996 0xd767c1c0f3800fcc

def z1039 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xf7ffc0e07ffe000f 0xffbffe0703fff000

def z1040 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xef003fe07f81f805 0xcf7801ff03fc0fc0

def z1041 : W := mkw 0x80922b190413854c 0x04049158c8209c2a 0x7ebe3f118c7f87ff 0x7bf5f1f88c63fc3f

def z1042 : W := mkw 0x8fb7bedd8012815f 0x047dbdf6ec00940a 0xffffffff807f81f7 0xfffffffffc03fc0f

def z1043 : W := mkw 0x072515a02e855610 0x903928ad01742ab0 0xff063fe07f87fe1f 0xcff831ff03fc3ff0

def z1044 : W := mkw 0x0000010004010400 0x0000000800200820 0x728627118c7f87ff 0x7b9431388c63fc3f

def z1045 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xecf8381ff079f9f6 0xf767c1c0ff83cfcf

def z1046 : W := mkw 0x8002030104138544 0x0400101808209c2a 0x720627018c7f87ff 0x6b9031380c63fc3f

def z1047 : W := mkw 0x08b7bedd8000001f 0x0045bdf6ec000000 0x10ffc7ff80000001 0x3087fe3ffc000000

def z1048 : W := mkw 0x070015a02e815610 0x903800ad01740ab0 0xef003fe07fc9fe1f 0xff7801ff03fe4ff0

def z1049 : W := mkw 0x00d8281a5070a988 0x4806c140d283854c 0xecf8381e7079f99e 0xff67c1c0f383cfcc

def z1050 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xffffd8007ffe780e 0xbffffec003fff3c0

def z1051 : W := mkw 0x808223110413854c 0x0404111888209c2a 0x728627118c7e07e9 0x7b9431388c63f03f

def z1052 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xad79ffff80000001 0xfd6bcffffc000000

def z1053 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0x2141c0ff83c807fb 0x790a0e07fc1e403f

def z1054 : W := mkw 0x08b7bedd8000001f 0x0045bdf6ec000000 0x0879ffff80000001 0xc043cffffc000000

def z1055 : W := mkw 0x072d40003b2c0000 0xe0396a0001d96000 0x57bfc0003fb60004 0x02bdfe0001fdb000

def z1056 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xa141c0ff83c807e9 0xfd0a0e07fc1e403f

def z1057 : W := mkw 0x808223110413854c 0x0404111888209c2a 0xf2862711cc7fe7ff 0xff9431388e63ff3f

def z1058 : W := mkw 0x08b7aa5d8000000f 0x0045bd52ec000000 0xf3ffe7ff80000001 0xff9fff3ffc000000

def z1059 : W := mkw 0x0098281a1030a988 0x4804c140d081854c 0xecf8381e3031f994 0xd767c1c0f1818fcc

def z1060 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0x5fffffff80000001 0x3afffffffc000000

def z1061 : W := mkw 0x4000c066818862a2 0x2a000603340c4315 0xa141c0ff838867f9 0xfd0a0e07fc1c433f

def z1062 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffff80700007 0xfffffffffc038000

def z1063 : W := mkw 0x808223110413854c 0x0404111888209c2a 0xf3862711cfff87ff 0x7f9c31388e7ffc3f

def z1064 : W := mkw 0x076d54807b6c0010 0xe03b6aa403db6000 0xffffd8e07ffe000e 0xbffffec703fff000

def z1065 : W := mkw 0x0f2595e4ae815613 0x90792caf25740ab0 0x0301c7e00f800609 0x08180e3f007c0030

def z1066 : W := mkw 0x0fb5bcdc8000001b 0x007dade6e4000000 0xeff9fffe00000001 0xdf7fcffff0000000

def z1067 : W := mkw 0x808223110413854c 0x0404111888209c2a 0xf6fe27118c7f87ff 0x7fb7f1388c63fc3f

def z1068 : W := mkw 0x076d40007b6c0000 0xe03b6a0003db6000 0xf7ffc0007ff60006 0x17bffe0003ffb000

def z1069 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffff807e0001 0xfffffffffc03f000

def z1070 : W := mkw 0x4040c066c1c862a2 0x2a020603360e4315 0xa141c0ffc38067f1 0xfd0a0e07fe1c033f

def z1071 : W := mkw 0x0f379ecd80000017 0x0079bcf66c000000 0xff7fffef80000001 0xeffbffff7c000000

def z1072 : W := mkw 0x80922b190413854c 0x04049158c8209c2a 0x7a863f1f8c7f87ff 0xfbd431f8fc63fc3f

def z1073 : W := mkw 0x0fb7bedd8010811f 0x007dbdf6ec008408 0xffffffff80018191 0xfffffffffc000c0c

def z1074 : W := mkw 0x0058080a50602880 0x4802c04052830144 0xcc78380e7001f804 0x8663c1c073800fc0

def z1075 : W := mkw 0x00da2a1b5070a98c 0x4806d150da83854c 0xfefe3f1ffc7ff99f 0xfff7f1f8ffe3ffcc

def z1076 : W := mkw 0x80da2a1b5072a9cc 0x4c06d150da83954e 0xfefe3f1ff07ff9f7 0xfff7f1f8ff83ffcf

def z1077 : W := mkw 0x0fb7bedd8000001f 0x007dbdf6ec000000 0xffffffff8000061b 0xfffffffffc000030

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z7,z5,z6]),(0,[z0,z8,z1,z2,z3,z5,z6]),(0,[z0,z9,z1,z2,z3,z5,z6]),(0,[z10,z0,z1,z2,z3,z5,z6])],[(0,[z11,z12,z1,z2,z3,z5,z6]),(0,[z0,z13,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z14,z3,z5,z6]),(0,[z0,z1,z15,z2,z3,z5,z6])],[(1,[z0,z1,z16,z17,z5,z6]),(0,[z0,z1,z2,z3,z5,z18,z6])],[(0,[z19,z0,z1,z2,z3,z5,z6]),(1,[z20,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z21,z5,z6]),(0,[z0,z1,z2,z22,z3,z5,z6]),(0,[z0,z1,z2,z3,z23,z6,z24]),(0,[z25,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z26,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z27])],[(0,[z0,z28,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z29,z6]),(0,[z30,z0,z1,z31,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z32,z6]),(0,[z33,z34,z1,z2,z3,z5,z6]),(0,[z35,z25,z1,z2,z3,z5,z6])],[(0,[z36,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z37,z6])]],
   [[(0,[z38,z0,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z39,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z40]),(0,[z0,z1,z2,z3,z5,z41,z6]),(0,[z0,z1,z2,z3,z5,z6,z42])],[(1,[z0,z1,z2,z3,z43,z6]),(0,[z44,z45,z1,z2,z3,z5,z6]),(0,[z46,z0,z1,z47,z3,z5,z6]),(0,[z48,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z49,z6]),(0,[z0,z2,z31,z3,z50,z5,z6]),(0,[z51,z0,z52,z1,z3,z5,z6]),(0,[z0,z1,z2,z53,z3,z5,z6]),(0,[z0,z1,z54,z2,z3,z5,z6])],[(0,[z55,z12,z1,z2,z3,z5,z6]),(0,[z56,z0,z1,z2,z3,z5,z6]),(0,[z57,z0,z1,z58,z3,z5,z6]),(1,[z59,z60,z0,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z61,z6])],[(0,[z0,z1,z2,z3,z62,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z63]),(1,[z0,z1,z2,z3,z5,z64]),(0,[z0,z1,z2,z65,z3,z5,z6]),(0,[z66,z0,z1,z2,z3,z5,z6]),(0,[z67,z0,z1,z2,z3,z5,z6]),(0,[z0,z68,z1,z2,z3,z5,z6])],[(0,[z57,z0,z1,z2,z3,z69,z6]),(0,[z0,z1,z2,z3,z70,z5,z6]),(0,[z71,z0,z1,z2,z72,z5,z6])],[(0,[z0,z1,z2,z3,z73,z5,z6]),(0,[z0,z74,z1,z2,z3,z5,z6]),(1,[z75,z0,z2,z3,z76,z6]),(0,[z77,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z78]),(0,[z0,z1,z79,z3,z5,z6,z80]),(0,[z0,z1,z81,z2,z3,z5,z82])],[(0,[z83,z0,z1,z2,z39,z5,z6]),(0,[z0,z84,z1,z2,z3,z5,z6]),(0,[z33,z0,z1,z3,z5,z23,z6]),(0,[z85,z0,z1,z2,z3,z86,z6]),(0,[z0,z1,z2,z3,z5,z87,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z6,z88]),(1,[z0,z89,z2,z3,z5,z6]),(0,[z0,z1,z90,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z91])],[(0,[z0,z1,z92,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z93,z5,z6]),(0,[z0,z1,z2,z3,z69,z5,z6]),(0,[z60,z0,z2,z31,z3,z5,z6]),(0,[z35,z0,z1,z2,z3,z5,z80])],[(0,[z0,z1,z2,z3,z5,z94,z6]),(0,[z12,z1,z2,z3,z95,z5,z6]),(0,[z0,z1,z2,z96,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z97,z6])],[(0,[z0,z1,z2,z3,z5,z6,z98]),(0,[z0,z1,z2,z3,z5,z99,z6]),(1,[z71,z0,z1,z2,z5,z100])],[(0,[z45,z1,z2,z101,z3,z5,z6]),(0,[z0,z102,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z103,z5,z6])],[(0,[z0,z1,z2,z3,z5,z104,z6]),(0,[z105,z0,z1,z2,z106,z5,z6]),(0,[z107,z0,z1,z2,z3,z5,z108]),(0,[z0,z1,z2,z3,z109,z5,z6])],[(0,[z0,z1,z2,z110,z3,z5,z6]),(0,[z0,z111,z1,z2,z3,z5,z6]),(1,[z112,z1,z2,z3,z5,z6]),(0,[z0,z1,z113,z2,z3,z5,z6])],[(0,[z45,z1,z2,z114,z3,z5,z6]),(0,[z0,z115,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z116,z6]),(1,[z30,z0,z1,z117,z5,z6]),(0,[z85,z0,z1,z2,z5,z118,z6]),(0,[z71,z119,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z72,z3,z5,z6]),(0,[z0,z1,z2,z5,z120,z6,z100])]],
   [[(1,[z0,z1,z2,z121,z5,z6]),(0,[z0,z1,z2,z3,z5,z122,z6]),(0,[z0,z1,z2,z3,z123,z5,z6]),(0,[z0,z1,z124,z2,z3,z5,z6]),(0,[z0,z52,z1,z2,z5,z6,z100]),(0,[z0,z1,z2,z125,z3,z5,z6]),(0,[z126,z0,z1,z2,z3,z5,z6]),(0,[z127,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z128,z129,z6]),(0,[z0,z1,z2,z130,z3,z5,z6]),(1,[z0,z131,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z132,z6]),(0,[z0,z119,z1,z2,z3,z5,z6]),(0,[z0,z133,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z134,z3,z5,z6])],[(0,[z135,z0,z1,z2,z3,z5,z6]),(0,[z136,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z137,z138]),(0,[z139,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z50,z17,z5,z6]),(0,[z140,z0,z1,z2,z3,z5,z6])],[(0,[z55,z0,z45,z2,z3,z5,z6]),(0,[z0,z1,z2,z141,z3,z5,z6]),(1,[z142,z1,z2,z3,z5,z6])],[(0,[z143,z0,z1,z2,z3,z5,z6]),(0,[z44,z83,z1,z2,z3,z5,z6]),(0,[z83,z0,z1,z2,z121,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z144]),(0,[z0,z1,z2,z3,z5,z145,z6]),(0,[z0,z1,z2,z3,z146,z5,z6])],[(0,[z0,z1,z147,z2,z3,z5,z6]),(0,[z148,z1,z2,z149,z3,z5,z6]),(0,[z0,z150,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z151,z5,z6]),(0,[z35,z0,z131,z2,z3,z5,z6]),(0,[z152,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z153])]],
   [[(0,[z0,z1,z2,z154,z3,z5,z6]),(0,[z155,z0,z1,z2,z3,z5,z6]),(0,[z156,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z157]),(0,[z0,z1,z2,z3,z5,z158,z6]),(0,[z0,z1,z2,z159,z86,z5,z6])],[(0,[z160,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z69,z76,z6]),(0,[z0,z161,z1,z2,z3,z5,z6]),(0,[z0,z162,z1,z2,z3,z5,z6]),(0,[z0,z52,z1,z2,z50,z5,z6]),(0,[z0,z1,z2,z72,z3,z5,z100])],[(0,[z0,z1,z2,z163,z3,z5,z6]),(0,[z0,z1,z164,z2,z3,z5,z6]),(0,[z0,z1,z165,z2,z3,z5,z6]),(0,[z0,z166,z1,z2,z3,z5,z6])],[],[(0,[z167,z0,z1,z2,z3,z5,z6]),(0,[z0,z102,z1,z2,z3,z76,z6]),(0,[z0,z1,z2,z168,z5,z137,z6]),(0,[z0,z1,z2,z3,z5,z6,z169])],[(0,[z57,z0,z1,z170,z3,z5,z6]),(0,[z1,z2,z3,z5,z129,z6,z138]),(0,[z0,z1,z2,z3,z5,z171,z6]),(0,[z172,z0,z1,z2,z3,z5,z6]),(0,[z173,z0,z1,z2,z3,z5,z6]),(0,[z35,z0,z1,z2,z174,z5,z6]),(0,[z0,z1,z2,z3,z175,z97,z6])],[(0,[z55,z176,z1,z2,z3,z5,z6]),(0,[z0,z1,z177,z2,z3,z5,z6]),(0,[z0,z1,z2,z170,z3,z5,z6]),(0,[z83,z1,z2,z3,z5,z6,z138]),(0,[z0,z1,z2,z3,z5,z178,z6]),(0,[z105,z0,z1,z2,z72,z5,z6]),(1,[z33,z0,z1,z3,z23,z6]),(0,[z0,z1,z2,z3,z179,z175,z6])]],
   [[(0,[z180,z0,z1,z2,z3,z5,z6]),(0,[z105,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z181,z5,z6]),(0,[z0,z1,z182,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z183]),(0,[z0,z1,z2,z3,z5,z6,z184]),(0,[z185,z0,z1,z2,z3,z5,z6]),(0,[z185,z0,z1,z2,z3,z5,z97])],[(0,[z55,z0,z1,z2,z3,z186,z6]),(0,[z187,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z188,z6]),(0,[z189,z1,z2,z149,z3,z5,z6]),(0,[z190,z0,z1,z2,z3,z5,z6]),(0,[z46,z1,z2,z3,z5,z129,z6]),(0,[z0,z1,z58,z2,z3,z5,z6]),(0,[z30,z0,z1,z16,z3,z5,z6])],[(0,[z189,z46,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z191]),(0,[z0,z1,z2,z3,z5,z192,z6]),(0,[z0,z1,z2,z3,z5,z6,z193])],[(0,[z0,z194,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z95,z5,z6,z100]),(0,[z0,z1,z2,z3,z5,z195,z6]),(1,[z0,z1,z2,z5,z6,z196])],[(0,[z0,z45,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z197,z5,z6]),(0,[z0,z52,z2,z3,z50,z5,z6]),(0,[z0,z1,z2,z3,z5,z198,z6]),(0,[z0,z1,z2,z3,z5,z6,z199])],[(0,[z176,z0,z1,z2,z3,z5,z6]),(0,[z200,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z201]),(0,[z0,z1,z2,z3,z17,z5,z6]),(0,[z0,z1,z2,z3,z179,z6,z24]),(0,[z202,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z43,z5,z6]),(0,[z0,z1,z2,z203,z3,z5,z6]),(0,[z0,z1,z204,z2,z3,z5,z6]),(0,[z30,z0,z1,z117,z3,z5,z6]),(0,[z0,z205,z1,z2,z3,z5,z6])],[(0,[z206,z0,z1,z2,z3,z5,z6]),(0,[z207,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z208,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z209,z6])]],
   [[(0,[z0,z1,z2,z210,z3,z5,z6]),(0,[z0,z1,z117,z3,z17,z5,z6]),(0,[z0,z1,z2,z211,z3,z5,z6])],[(0,[z0,z1,z2,z212,z3,z5,z6]),(0,[z0,z213,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z214])],[(0,[z57,z1,z2,z3,z5,z129,z6]),(0,[z0,z1,z2,z17,z5,z6,z100]),(0,[z0,z1,z2,z3,z5,z215,z6]),(0,[z0,z1,z2,z216,z3,z5,z6])],[(0,[z0,z1,z2,z217,z3,z5,z6]),(0,[z0,z20,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z218,z5,z6])],[(1,[z0,z1,z2,z62,z5,z6]),(1,[z55,z2,z101,z3,z5,z6]),(0,[z1,z47,z2,z149,z3,z5,z6]),(0,[z0,z1,z2,z3,z69,z128,z6]),(0,[z0,z1,z2,z3,z5,z219,z6]),(0,[z0,z1,z2,z3,z5,z6,z220]),(1,[z0,z1,z81,z3,z5,z82]),(1,[z0,z1,z221,z3,z5,z6])],[(0,[z0,z1,z47,z3,z5,z23,z6]),(0,[z11,z1,z2,z114,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z222]),(1,[z1,z2,z223,z3,z5,z6]),(0,[z0,z1,z2,z3,z224,z5,z6]),(0,[z71,z0,z1,z2,z5,z6,z100])],[(0,[z225,z0,z1,z2,z3,z5,z6]),(0,[z60,z0,z1,z149,z3,z5,z6]),(0,[z0,z1,z2,z226,z3,z5,z6]),(0,[z12,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z227,z6]),(0,[z0,z228,z1,z2,z3,z5,z6]),(0,[z229,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z81,z3,z5,z82,z6])]],
   [[(0,[z230,z0,z1,z2,z3,z5,z6]),(0,[z0,z102,z1,z2,z3,z128,z6])],[(0,[z231,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z138,z100]),(0,[z0,z1,z2,z232,z3,z5,z6]),(0,[z0,z233,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z234])],[(0,[z0,z1,z2,z235,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z138,z108]),(0,[z35,z0,z1,z2,z3,z5,z82])],[(0,[z148,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z236,z3,z5,z6]),(0,[z0,z1,z2,z237,z3,z5,z6]),(0,[z107,z0,z2,z3,z5,z6,z108]),(0,[z238,z0,z1,z2,z3,z5,z6])],[(0,[z55,z0,z1,z210,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z239,z6]),(0,[z0,z1,z2,z159,z3,z118,z6])],[(0,[z240,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z241,z6]),(0,[z0,z1,z2,z3,z5,z6,z242]),(0,[z0,z115,z1,z2,z232,z5,z6]),(0,[z0,z1,z243,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z244,z5,z6]),(0,[z0,z1,z245,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z246])],[(1,[z46,z1,z47,z3,z5,z6]),(0,[z247,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z248,z3,z5,z6]),(0,[z0,z1,z249,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z250,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z251]),(0,[z0,z1,z2,z3,z252,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z253])],[(0,[z0,z1,z2,z3,z5,z254,z6]),(0,[z0,z1,z2,z3,z129,z76,z6]),(1,[z51,z0,z1,z3,z5,z6]),(0,[z0,z1,z255,z2,z3,z5,z6]),(1,[z0,z256,z2,z3,z5,z6])],[(0,[z0,z257,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z64]),(1,[z258,z1,z2,z3,z5,z6]),(0,[z0,z16,z89,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z259,z6]),(0,[z260,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z31,z149,z3,z5,z6]),(0,[z0,z1,z2,z3,z261,z5,z6]),(0,[z0,z2,z31,z3,z5,z6,z108]),(0,[z262,z0,z1,z2,z3,z5,z6]),(0,[z263,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z264,z5,z6]),(0,[z33,z0,z1,z2,z3,z179,z6]),(0,[z0,z1,z2,z3,z5,z265,z6])],[(0,[z189,z0,z1,z2,z3,z5,z6]),(0,[z189,z0,z1,z47,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z266]),(0,[z267,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z120,z138]),(0,[z0,z1,z2,z3,z5,z6,z268]),(0,[z0,z233,z1,z2,z3,z5,z108]),(0,[z0,z233,z1,z2,z3,z5,z137]),(0,[z0,z1,z2,z3,z5,z269,z6])],[(0,[z0,z1,z270,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z271,z6]),(0,[z0,z1,z2,z3,z5,z272,z6])],[(1,[z0,z1,z273,z3,z5,z6]),(0,[z0,z1,z274,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z275]),(0,[z0,z1,z2,z3,z5,z276,z6]),(0,[z0,z112,z1,z2,z3,z5,z6]),(0,[z0,z1,z277,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z278,z5,z6]),(0,[z279,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z280,z3,z5,z6]),(0,[z85,z0,z1,z2,z159,z5,z6]),(1,[z85,z0,z1,z2,z118,z6]),(0,[z185,z0,z277,z2,z3,z5,z6]),(1,[z0,z1,z2,z281,z5,z6]),(0,[z282,z0,z1,z2,z3,z5,z6])],[(0,[z55,z0,z1,z2,z217,z5,z6]),(0,[z0,z1,z2,z3,z5,z283,z6])],[(0,[z55,z0,z1,z2,z3,z5,z284])],[(0,[z0,z1,z2,z3,z5,z6,z285]),(0,[z0,z1,z2,z3,z286,z5,z6]),(0,[z0,z115,z2,z31,z3,z5,z6]),(0,[z0,z1,z287,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z288,z5,z6]),(0,[z289,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z72,z95,z5,z6]),(0,[z0,z1,z2,z3,z5,z290,z6]),(0,[z0,z1,z2,z3,z5,z291,z6]),(0,[z0,z1,z2,z3,z5,z6,z292]),(0,[z0,z1,z2,z3,z5,z293,z6])],[(0,[z46,z0,z1,z2,z3,z5,z6]),(0,[z12,z0,z1,z2,z114,z5,z6]),(0,[z0,z233,z102,z2,z3,z5,z6]),(1,[z140,z0,z2,z3,z5,z6]),(0,[z0,z256,z1,z2,z3,z5,z6]),(0,[z294,z0,z1,z2,z3,z5,z6])],[(0,[z295,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z296,z3,z5,z6]),(0,[z297,z0,z1,z2,z3,z5,z6]),(0,[z0,z142,z1,z2,z3,z5,z6])],[(0,[z298,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z137,z6,z196]),(1,[z0,z1,z299,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z300,z3,z5,z6]),(0,[z0,z1,z301,z2,z3,z5,z6]),(0,[z0,z1,z302,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z303]),(0,[z105,z0,z1,z2,z5,z6,z100]),(0,[z0,z1,z304,z2,z3,z5,z6]),(0,[z33,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z305])],[(0,[z12,z0,z1,z2,z3,z5,z94]),(0,[z306,z0,z1,z2,z3,z5,z6]),(1,[z105,z0,z2,z106,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z138]),(0,[z0,z1,z2,z307,z3,z5,z6]),(0,[z75,z0,z1,z2,z3,z76,z6])],[(0,[z308,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z309,z3,z5,z6]),(1,[z34,z1,z2,z3,z5,z6]),(0,[z0,z310,z1,z2,z3,z5,z6])],[(0,[z55,z44,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z311,z3,z5,z6]),(0,[z30,z60,z0,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z312,z5,z6])],[(0,[z0,z1,z2,z106,z114,z5,z6]),(0,[z57,z0,z1,z2,z3,z129,z6]),(0,[z75,z0,z102,z2,z3,z5,z6])],[(0,[z313,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z314,z6]),(0,[z0,z315,z1,z2,z3,z5,z6])],[(0,[z57,z0,z1,z2,z3,z5,z6]),(0,[z59,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z316,z6]),(1,[z0,z52,z2,z50,z5,z6]),(0,[z0,z1,z2,z72,z5,z118,z6])],[(0,[z46,z148,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z317,z5,z6]),(0,[z318,z0,z1,z2,z3,z5,z6]),(0,[z34,z0,z1,z2,z3,z5,z6])],[(0,[z319,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z320,z3,z5,z6]),(0,[z105,z0,z1,z2,z50,z5,z6]),(0,[z0,z321,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z322,z5,z6])],[(0,[z11,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z323,z6]),(0,[z324,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z325,z5,z6]),(0,[z0,z1,z79,z2,z3,z179,z6]),(0,[z0,z326,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z327,z3,z5,z6])],[(0,[z189,z0,z1,z2,z3,z328,z6]),(0,[z1,z2,z149,z3,z5,z6,z138]),(0,[z105,z0,z2,z31,z3,z5,z6]),(0,[z0,z1,z2,z159,z5,z6,z100]),(1,[z202,z1,z2,z3,z5,z6])],[(0,[z329,z0,z1,z2,z3,z5,z6]),(0,[z0,z115,z1,z31,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z330,z6])],[(0,[z55,z0,z2,z101,z3,z5,z6]),(0,[z0,z1,z2,z331,z3,z5,z6])],[(0,[z332,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z333,z6]),(0,[z35,z112,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z334,z2,z3,z5,z6]),(0,[z0,z1,z2,z335,z3,z5,z6])],[(1,[z0,z1,z2,z3,z186,z6]),(0,[z0,z1,z2,z336,z3,z5,z6]),(0,[z337,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z338,z6]),(0,[z0,z1,z2,z3,z86,z5,z6])],[(0,[z59,z0,z233,z2,z3,z5,z6])],[(0,[z0,z1,z2,z101,z3,z5,z6]),(0,[z57,z148,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z339,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z340]),(0,[z341,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z342,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z343])],[(0,[z0,z1,z2,z3,z344,z5,z6]),(0,[z83,z0,z1,z2,z3,z5,z138])],[(0,[z55,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z345,z6]),(0,[z1,z2,z3,z69,z5,z129,z6]),(0,[z0,z1,z2,z3,z5,z6,z346]),(0,[z75,z0,z1,z2,z3,z128,z6]),(0,[z347,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z114,z3,z5,z6]),(0,[z0,z348,z1,z2,z3,z5,z6]),(0,[z185,z0,z1,z2,z3,z175,z6])],[(0,[z0,z1,z2,z349,z3,z5,z6]),(0,[z0,z1,z2,z223,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z350]),(0,[z0,z1,z79,z2,z3,z5,z6])]],
   [[(0,[z83,z0,z1,z2,z3,z5,z351]),(0,[z0,z1,z2,z3,z5,z6,z352]),(0,[z0,z1,z79,z81,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z353,z6]),(1,[z0,z1,z2,z3,z354,z6])],[(0,[z176,z0,z2,z101,z3,z5,z6]),(0,[z355,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z356,z2,z3,z5,z6]),(0,[z357,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z358,z6])],[(0,[z0,z1,z1,z2,z3,z5,z6]),(0,[z359,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z72,z5,z120,z6]),(0,[z360,z0,z1,z2,z3,z5,z6])],[(0,[z361,z0,z1,z2,z3,z5,z6]),(0,[z0,z362,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z363,z3,z5,z6]),(0,[z140,z0,z16,z2,z3,z5,z6])],[(0,[z12,z0,z1,z2,z95,z5,z6]),(0,[z1,z2,z114,z3,z95,z5,z6]),(1,[z0,z1,z170,z3,z5,z6]),(0,[z0,z1,z2,z3,z364,z5,z6]),(0,[z185,z0,z1,z2,z3,z6,z24])],[(0,[z0,z1,z2,z3,z5,z6,z365]),(0,[z44,z0,z1,z2,z3,z5,z138]),(0,[z60,z0,z115,z1,z3,z5,z6]),(0,[z0,z233,z2,z31,z3,z5,z6]),(0,[z0,z233,z2,z3,z5,z137,z6]),(0,[z0,z1,z2,z159,z3,z86,z6])],[(0,[z366,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z367]),(0,[z105,z0,z52,z2,z3,z5,z6]),(0,[z0,z1,z368,z2,z3,z5,z6])],[(0,[z0,z369,z1,z2,z3,z5,z6]),(0,[z0,z1,z370,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z137,z6,z108])]],
   [[(0,[z0,z1,z2,z3,z5,z186,z6]),(0,[z371,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z372,z6]),(0,[z44,z0,z1,z2,z3,z5,z351])],[(0,[z0,z1,z2,z3,z373,z5,z6]),(0,[z374,z0,z1,z2,z3,z5,z6]),(0,[z0,z375,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z376,z6])],[(0,[z0,z1,z2,z3,z5,z6,z377]),(0,[z0,z1,z2,z3,z5,z6,z378])],[(0,[z0,z1,z2,z3,z3,z5,z6]),(0,[z0,z1,z2,z106,z95,z5,z6])],[(1,[z0,z1,z210,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z379,z6]),(0,[z0,z1,z2,z3,z5,z6,z380]),(0,[z0,z1,z2,z3,z5,z6,z381]),(0,[z0,z382,z1,z2,z3,z5,z6]),(0,[z0,z131,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z383,z5,z6]),(0,[z384,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z47,z2,z3,z5,z6]),(0,[z385,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z386,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z354,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z387,z6]),(0,[z0,z1,z2,z388,z3,z5,z6]),(0,[z0,z1,z2,z389,z3,z5,z6])],[(0,[z390,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z391]),(0,[z0,z1,z2,z3,z392,z5,z6]),(0,[z30,z0,z1,z2,z17,z5,z6]),(0,[z0,z1,z81,z3,z5,z23,z6]),(0,[z0,z1,z2,z3,z5,z6,z393]),(0,[z0,z1,z394,z2,z3,z5,z6])],[(0,[z395,z0,z1,z2,z3,z5,z6]),(0,[z396,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z397,z3,z5,z6]),(0,[z0,z1,z2,z398,z3,z5,z6]),(0,[z399,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z400,z6]),(0,[z401,z71,z1,z2,z3,z5,z6])],[(0,[z189,z0,z1,z2,z3,z392,z6]),(0,[z402,z0,z1,z2,z3,z5,z6]),(0,[z403,z0,z1,z2,z3,z5,z6]),(0,[z0,z404,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z405,z6])],[(0,[z406,z0,z1,z2,z3,z5,z6]),(0,[z148,z0,z1,z2,z3,z129,z6]),(0,[z0,z1,z2,z3,z69,z23,z6]),(0,[z407,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z408])],[(0,[z0,z1,z2,z3,z5,z6,z409]),(0,[z0,z1,z2,z3,z175,z5,z97])],[(0,[z148,z1,z2,z3,z69,z5,z6]),(0,[z0,z1,z410,z2,z3,z5,z6])],[(0,[z0,z1,z411,z2,z3,z5,z6]),(0,[z412,z0,z1,z2,z3,z5,z6]),(0,[z413,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z414,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z415,z5,z6]),(0,[z0,z1,z2,z3,z416,z5,z6])],[(0,[z0,z1,z2,z3,z417,z5,z6]),(0,[z0,z418,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z284]),(0,[z55,z0,z1,z2,z3,z5,z419]),(1,[z0,z1,z2,z317,z5,z6]),(0,[z0,z2,z3,z128,z5,z76,z6]),(0,[z0,z1,z3,z5,z23,z6,z80])],[(0,[z0,z1,z2,z3,z5,z420,z6]),(0,[z0,z1,z2,z421,z3,z5,z6]),(0,[z422,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z423])],[(0,[z0,z2,z106,z3,z50,z5,z6]),(0,[z75,z0,z1,z2,z3,z5,z6])],[(0,[z105,z59,z0,z2,z3,z5,z6]),(0,[z424,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z425,z5,z6]),(0,[z426,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z427,z6]),(0,[z0,z1,z2,z428,z3,z5,z6]),(0,[z59,z60,z0,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z429,z6]),(0,[z44,z1,z2,z3,z95,z5,z6]),(0,[z0,z1,z2,z3,z5,z430,z6]),(0,[z431,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z432]),(0,[z185,z0,z1,z2,z3,z5,z24])]],
   [[(0,[z0,z1,z433,z2,z3,z5,z6]),(0,[z0,z434,z1,z2,z3,z5,z6])],[(0,[z435,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z436,z3,z5,z6]),(0,[z0,z437,z1,z2,z3,z5,z6]),(0,[z0,z1,z221,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z438,z6]),(0,[z0,z1,z439,z2,z3,z5,z6])],[(0,[z59,z0,z2,z3,z5,z6,z108]),(0,[z0,z1,z2,z3,z440,z5,z6]),(0,[z0,z1,z2,z441,z3,z5,z6]),(0,[z0,z102,z2,z3,z5,z6,z108]),(0,[z0,z1,z2,z3,z5,z442,z6])],[(0,[z176,z45,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z443,z3,z5,z6]),(0,[z444,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z445,z5,z6]),(0,[z0,z446,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z120,z351]),(0,[z0,z233,z2,z3,z5,z76,z6])],[(0,[z0,z1,z2,z3,z5,z447,z6]),(0,[z11,z44,z1,z2,z3,z5,z6]),(1,[z83,z1,z2,z3,z5,z138]),(0,[z35,z0,z1,z3,z5,z6,z80]),(0,[z401,z0,z1,z2,z3,z5,z6])],[(0,[z448,z0,z1,z2,z3,z5,z6]),(0,[z449,z0,z1,z2,z3,z5,z6]),(0,[z46,z1,z2,z3,z5,z6,z138]),(0,[z450,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z451,z6])],[(0,[z452,z0,z1,z2,z3,z5,z6]),(0,[z71,z0,z1,z2,z3,z5,z120])]],
   [[(0,[z44,z1,z2,z149,z3,z5,z6]),(0,[z0,z1,z2,z453,z3,z5,z6]),(1,[z35,z0,z1,z3,z5,z80]),(0,[z0,z1,z454,z2,z3,z5,z6])],[(0,[z44,z46,z1,z2,z3,z5,z6]),(0,[z455,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z456]),(0,[z0,z1,z2,z3,z5,z6,z6]),(0,[z0,z1,z2,z3,z5,z457,z6]),(0,[z0,z1,z458,z2,z3,z5,z6]),(1,[z0,z1,z2,z168,z5,z6])],[(0,[z0,z2,z3,z5,z76,z6,z108]),(1,[z0,z102,z2,z3,z128,z6]),(0,[z0,z1,z2,z3,z5,z82,z6])],[(0,[z0,z1,z2,z3,z5,z459,z6]),(0,[z59,z0,z2,z3,z50,z5,z6]),(0,[z0,z1,z2,z3,z5,z460,z6]),(0,[z85,z0,z1,z2,z3,z5,z6])],[(1,[z0,z1,z58,z3,z5,z6]),(1,[z44,z1,z2,z3,z5,z351]),(1,[z0,z115,z31,z3,z5,z6]),(0,[z75,z0,z2,z3,z5,z76,z6]),(0,[z0,z1,z2,z3,z5,z6,z461])],[(0,[z12,z45,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z462,z3,z5,z6]),(0,[z0,z1,z2,z463,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z464,z6]),(0,[z0,z1,z2,z465,z3,z5,z6])],[(0,[z466,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z467,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z468,z5,z6]),(0,[z469,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z470,z6]),(1,[z471,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z472,z5,z6]),(0,[z473,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z50,z95,z5,z6]),(0,[z0,z1,z2,z3,z5,z474,z6]),(0,[z0,z1,z2,z3,z475,z5,z6])],[(0,[z0,z1,z2,z3,z476,z5,z6]),(0,[z0,z1,z2,z3,z477,z5,z6]),(0,[z0,z1,z2,z478,z3,z5,z6])],[(0,[z0,z1,z89,z2,z3,z5,z6])],[(0,[z479,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z480,z5,z6]),(0,[z0,z1,z2,z3,z129,z23,z6]),(0,[z0,z1,z16,z2,z117,z5,z6])],[(0,[z481,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z137,z6,z482]),(0,[z0,z1,z2,z483,z3,z5,z6]),(0,[z0,z1,z2,z484,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z485,z6]),(0,[z0,z1,z2,z3,z5,z6,z100]),(0,[z486,z0,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z487,z5,z6]),(0,[z59,z0,z1,z31,z3,z5,z6]),(0,[z488,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z31,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z137,z6]),(0,[z0,z1,z2,z3,z489,z5,z6])],[(0,[z189,z0,z1,z149,z3,z5,z6]),(0,[z490,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z179,z69,z6]),(0,[z0,z1,z2,z3,z5,z6,z491])]],
   [[(0,[z492,z0,z1,z2,z3,z5,z6]),(0,[z493,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z494,z2,z3,z5,z6]),(1,[z401,z1,z2,z3,z5,z6])],[(0,[z495,z0,z1,z2,z3,z5,z6])],[(1,[z148,z1,z2,z3,z69,z6]),(0,[z0,z496,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z497,z6]),(0,[z51,z0,z1,z2,z3,z5,z6]),(0,[z30,z0,z1,z2,z117,z5,z6])],[(0,[z498,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z121,z3,z5,z6]),(0,[z499,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z500,z3,z5,z6])],[(0,[z501,z0,z1,z2,z3,z5,z6]),(0,[z502,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z503,z5,z6]),(0,[z0,z1,z2,z504,z3,z5,z6])],[(0,[z55,z1,z2,z3,z5,z6,z138]),(0,[z0,z1,z2,z505,z3,z5,z6]),(0,[z12,z0,z1,z2,z3,z5,z64]),(0,[z0,z1,z506,z2,z3,z5,z6]),(0,[z507,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z50,z5,z6])],[(0,[z46,z0,z1,z149,z3,z5,z6]),(0,[z508,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z509])]],
   [[(0,[z0,z1,z510,z2,z3,z5,z6]),(0,[z0,z1,z2,z114,z72,z5,z6]),(0,[z1,z2,z3,z5,z351,z6,z138]),(0,[z59,z60,z0,z1,z3,z5,z6]),(0,[z511,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z512,z6]),(0,[z185,z142,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z95,z5,z6]),(0,[z513,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z514,z3,z5,z6]),(0,[z515,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z516,z2,z3,z5,z6])],[(0,[z0,z1,z2,z517,z3,z5,z6]),(0,[z0,z1,z2,z518,z3,z5,z6]),(0,[z519,z0,z1,z2,z3,z5,z6]),(0,[z520,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z521,z6]),(0,[z0,z1,z2,z522,z3,z5,z6])],[],[(0,[z523,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z5,z6]),(0,[z44,z0,z1,z2,z3,z5,z6]),(0,[z524,z0,z1,z2,z3,z5,z6])],[(0,[z0,z525,z1,z2,z3,z5,z6]),(0,[z0,z526,z1,z2,z3,z5,z6]),(0,[z0,z52,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z527,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z528])],[(0,[z529,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z351,z137]),(0,[z0,z1,z2,z3,z5,z530,z6]),(0,[z0,z1,z2,z3,z5,z531,z6])]],
   [[(0,[z532,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z533,z6]),(0,[z534,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z535,z2,z3,z5,z6]),(1,[z11,z1,z2,z114,z5,z6]),(0,[z35,z0,z1,z2,z3,z354,z6])],[(0,[z0,z1,z2,z149,z3,z5,z6]),(0,[z0,z1,z536,z2,z3,z5,z6]),(0,[z35,z0,z1,z2,z3,z358,z6]),(0,[z0,z1,z2,z3,z5,z537,z6])],[(0,[z0,z1,z2,z117,z106,z5,z6]),(0,[z0,z1,z2,z3,z538,z5,z6]),(0,[z0,z1,z2,z3,z539,z5,z6])],[(1,[z0,z1,z2,z3,z328,z6]),(0,[z1,z2,z149,z3,z5,z129,z6]),(0,[z11,z0,z1,z2,z114,z5,z6]),(1,[z0,z233,z2,z3,z5,z137]),(0,[z471,z1,z2,z3,z5,z137,z6]),(0,[z0,z1,z2,z3,z5,z6,z540]),(0,[z0,z1,z2,z3,z174,z5,z6])],[(0,[z0,z1,z541,z2,z3,z5,z6]),(0,[z0,z1,z16,z2,z17,z5,z6])],[(1,[z189,z1,z149,z3,z5,z6]),(0,[z542,z0,z1,z2,z3,z5,z6]),(0,[z33,z20,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z543,z6])],[(0,[z0,z1,z544,z2,z3,z5,z6]),(1,[z0,z255,z2,z3,z5,z6]),(0,[z0,z1,z2,z86,z5,z118,z6])]],
   [[(0,[z0,z545,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z546]),(0,[z547,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z548,z6])],[(0,[z0,z1,z2,z3,z5,z6,z284]),(0,[z0,z1,z2,z3,z5,z549,z6]),(0,[z0,z115,z1,z2,z317,z5,z6]),(0,[z0,z1,z16,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z550,z6]),(0,[z551,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z552])],[(0,[z553,z0,z1,z2,z3,z5,z6]),(0,[z105,z0,z2,z106,z3,z5,z6]),(0,[z0,z1,z81,z2,z3,z5,z6]),(0,[z0,z1,z2,z554,z3,z5,z6])],[(1,[z12,z1,z2,z95,z5,z6]),(0,[z555,z0,z1,z2,z3,z5,z6]),(0,[z33,z0,z1,z2,z3,z23,z6]),(0,[z0,z1,z2,z3,z5,z6,z556])],[(0,[z557,z0,z1,z2,z3,z5,z6]),(0,[z0,z558,z1,z2,z3,z5,z6])],[(0,[z0,z1,z47,z31,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z559,z6]),(0,[z0,z1,z2,z3,z5,z560,z6]),(0,[z0,z1,z2,z3,z561,z5,z6]),(0,[z0,z1,z2,z3,z5,z76,z6]),(1,[z25,z1,z2,z3,z5,z6]),(0,[z35,z0,z255,z2,z3,z5,z6]),(1,[z0,z277,z2,z3,z5,z6])],[(0,[z0,z1,z273,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z419,z6]),(0,[z562,z0,z1,z2,z3,z5,z6])],[(0,[z148,z1,z2,z3,z5,z6,z138]),(0,[z0,z1,z31,z3,z17,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z196]),(0,[z0,z1,z2,z3,z5,z6,z563]),(0,[z35,z0,z1,z2,z383,z5,z6]),(0,[z185,z0,z1,z2,z218,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z564])]],
   [[(0,[z45,z1,z2,z3,z5,z6,z138]),(0,[z0,z1,z2,z3,z5,z565,z6]),(0,[z0,z1,z2,z3,z566,z5,z6]),(0,[z30,z0,z1,z2,z3,z5,z6]),(0,[z185,z0,z1,z221,z3,z5,z6]),(0,[z0,z1,z2,z3,z175,z5,z6])],[(0,[z0,z1,z79,z149,z3,z5,z6]),(0,[z0,z1,z2,z3,z567,z5,z6]),(0,[z568,z0,z1,z2,z3,z5,z6])],[(0,[z569,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z328,z6]),(0,[z0,z1,z2,z3,z570,z5,z6]),(0,[z0,z1,z2,z3,z5,z571,z6])],[(0,[z572,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z217,z5,z6]),(0,[z44,z1,z2,z3,z5,z351,z6]),(0,[z0,z573,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z232,z5,z6])],[(0,[z59,z0,z115,z2,z3,z5,z6]),(0,[z0,z102,z2,z3,z128,z5,z6]),(0,[z0,z1,z2,z117,z72,z5,z6])],[(0,[z0,z1,z2,z574,z3,z5,z6]),(0,[z1,z2,z223,z3,z50,z5,z6]),(0,[z0,z1,z575,z2,z3,z5,z6]),(0,[z107,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z576,z3,z5,z6]),(0,[z0,z1,z2,z117,z3,z5,z6]),(0,[z577,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z578,z5,z6]),(0,[z258,z1,z2,z3,z50,z5,z6]),(0,[z0,z1,z2,z3,z5,z579,z6]),(0,[z0,z1,z2,z3,z580,z5,z6]),(0,[z0,z1,z2,z3,z5,z120,z6]),(0,[z0,z1,z2,z299,z3,z5,z6])]],
   [[(0,[z581,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z582,z6]),(0,[z0,z1,z2,z3,z218,z5,z6])],[],[(0,[z583,z0,z1,z2,z3,z5,z6]),(0,[z584,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z585,z5,z6]),(0,[z0,z1,z2,z3,z5,z586,z6]),(0,[z0,z1,z2,z587,z3,z5,z6])],[(0,[z44,z1,z2,z3,z5,z129,z6]),(0,[z0,z1,z2,z3,z5,z588,z6]),(0,[z0,z1,z2,z589,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z590]),(0,[z71,z0,z1,z2,z3,z5,z6])],[(0,[z55,z0,z1,z273,z3,z5,z6]),(0,[z591,z0,z1,z2,z3,z5,z6]),(0,[z592,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z72,z159,z5,z6]),(0,[z185,z0,z256,z2,z3,z5,z6])],[(0,[z593,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z594,z6]),(1,[z1,z2,z3,z5,z6,z482]),(0,[z595,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z596])],[(0,[z0,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z47,z79,z3,z5,z6]),(0,[z597,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z358,z5,z6]),(1,[z0,z1,z2,z159,z86,z6])],[(0,[z0,z1,z2,z598,z3,z5,z6])]],
   [[(0,[z599,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z72,z17,z5,z6])],[(0,[z0,z1,z2,z600,z3,z5,z6]),(0,[z0,z1,z2,z114,z5,z6,z100]),(0,[z0,z1,z2,z3,z5,z601,z6]),(0,[z107,z0,z233,z2,z3,z5,z6]),(0,[z0,z1,z16,z3,z17,z5,z6])],[(0,[z55,z0,z1,z2,z3,z43,z6]),(0,[z0,z1,z2,z3,z602,z5,z6]),(0,[z0,z1,z603,z2,z3,z5,z6]),(0,[z107,z0,z1,z2,z3,z5,z137]),(0,[z604,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z79,z2,z3,z23,z6])],[(1,[z0,z1,z2,z3,z392,z6]),(0,[z11,z0,z1,z2,z95,z5,z6]),(0,[z605,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z606,z5,z6]),(0,[z185,z0,z1,z2,z281,z5,z6])],[(0,[z0,z607,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z608,z5,z6]),(0,[z0,z1,z2,z3,z5,z23,z6]),(0,[z609,z0,z1,z2,z3,z5,z6]),(0,[z610,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z611,z5,z6])],[(0,[z0,z1,z2,z3,z5,z612,z6]),(0,[z71,z0,z1,z2,z3,z5,z100])],[]],
   [[(0,[z0,z613,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z128,z5,z6]),(0,[z614,z0,z1,z2,z3,z5,z6]),(0,[z615,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z616])],[(0,[z0,z617,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z618,z5,z6]),(0,[z0,z1,z2,z3,z5,z619,z6])],[(0,[z0,z1,z2,z620,z3,z5,z6]),(1,[z0,z1,z307,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z621,z6]),(0,[z185,z0,z1,z299,z3,z5,z6])],[(0,[z0,z1,z2,z114,z50,z5,z6]),(0,[z0,z1,z2,z622,z3,z5,z6]),(0,[z0,z1,z623,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z624,z5,z6]),(0,[z0,z1,z2,z72,z3,z5,z120]),(1,[z0,z1,z2,z3,z175,z97])],[(0,[z0,z1,z2,z625,z3,z5,z6]),(0,[z626,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z627]),(0,[z0,z1,z2,z3,z175,z5,z24]),(0,[z628,z0,z1,z2,z3,z5,z6])],[(0,[z60,z0,z1,z47,z3,z5,z6]),(0,[z60,z0,z1,z2,z3,z5,z6]),(0,[z0,z52,z1,z2,z106,z5,z6]),(0,[z0,z1,z3,z179,z5,z23,z6]),(1,[z0,z1,z2,z174,z5,z6])],[(0,[z0,z1,z2,z629,z3,z5,z6]),(0,[z630,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z631])],[(0,[z11,z1,z2,z3,z5,z6,z138]),(0,[z0,z1,z2,z632,z3,z5,z6]),(0,[z85,z0,z1,z2,z3,z118,z6])]],
   [[(0,[z0,z1,z2,z3,z39,z5,z6]),(0,[z633,z0,z1,z2,z3,z5,z6]),(0,[z634,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z108]),(0,[z0,z1,z2,z635,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z636])],[(0,[z637,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z638,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z639]),(0,[z0,z1,z2,z640,z3,z5,z6])],[(1,[z107,z0,z2,z3,z5,z108]),(0,[z471,z0,z1,z2,z3,z5,z6])],[(0,[z176,z0,z45,z2,z3,z5,z6]),(0,[z0,z1,z641,z2,z3,z5,z6]),(0,[z0,z1,z81,z2,z3,z5,z80])],[(0,[z642,z0,z1,z2,z3,z5,z6]),(0,[z83,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z351,z6]),(0,[z0,z1,z2,z643,z3,z5,z6]),(0,[z35,z0,z1,z2,z3,z5,z6]),(0,[z644,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z179,z129,z6]),(0,[z35,z0,z1,z81,z3,z5,z6]),(0,[z645,z0,z1,z2,z3,z5,z6]),(0,[z185,z202,z1,z2,z3,z5,z6])]],
   [[(0,[z646,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z647,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z648,z6]),(0,[z0,z1,z2,z3,z175,z23,z6]),(1,[z0,z1,z79,z3,z179,z6]),(0,[z0,z1,z2,z3,z5,z6,z649])],[(0,[z650,z0,z1,z2,z3,z5,z6]),(0,[z0,z651,z1,z2,z3,z5,z6]),(0,[z652,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z179,z5,z6]),(1,[z119,z1,z2,z3,z5,z6])],[(0,[z653,z0,z1,z2,z3,z5,z6]),(0,[z0,z52,z1,z307,z3,z5,z6]),(0,[z33,z0,z1,z79,z3,z5,z6]),(0,[z0,z1,z2,z654,z3,z5,z6])],[(0,[z0,z1,z2,z655,z3,z5,z6]),(1,[z185,z0,z1,z2,z3,z24])],[],[(0,[z0,z1,z2,z3,z5,z129,z6]),(0,[z656,z0,z1,z2,z3,z5,z6]),(0,[z657,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z658,z3,z5,z6]),(0,[z0,z1,z2,z3,z659,z5,z6]),(0,[z660,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z281,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z661]),(0,[z0,z1,z2,z3,z662,z5,z6]),(0,[z663,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z117,z5,z6,z100]),(0,[z664,z0,z1,z2,z3,z5,z6]),(0,[z665,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z666,z3,z5,z6]),(0,[z1,z2,z3,z95,z5,z6,z138]),(0,[z0,z1,z2,z3,z5,z667,z6]),(0,[z668,z0,z1,z2,z3,z5,z6]),(0,[z0,z52,z1,z2,z72,z5,z6]),(0,[z258,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z669,z0,z1,z2,z3,z5,z6]),(1,[z57,z1,z2,z3,z129,z6]),(0,[z0,z1,z2,z670,z3,z5,z6]),(0,[z0,z1,z2,z671,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z672,z6]),(0,[z0,z1,z2,z3,z5,z6,z24])],[(0,[z0,z1,z2,z3,z5,z673,z6]),(0,[z148,z0,z1,z2,z3,z69,z6]),(0,[z0,z1,z2,z3,z5,z351,z100]),(0,[z0,z1,z2,z3,z5,z6,z674]),(0,[z0,z1,z2,z3,z5,z6,z675]),(0,[z0,z1,z2,z159,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z351,z108]),(0,[z0,z1,z2,z383,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z676])],[(0,[z677,z0,z1,z2,z3,z5,z6]),(0,[z0,z678,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z679,z3,z5,z6])],[(0,[z0,z680,z1,z2,z3,z5,z6])],[(0,[z681,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z682,z3,z5,z6]),(0,[z60,z0,z1,z3,z17,z5,z6])],[(0,[z46,z1,z47,z2,z3,z5,z6]),(0,[z683,z0,z1,z2,z3,z5,z6]),(0,[z0,z684,z1,z2,z3,z5,z6]),(0,[z0,z685,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z686,z6]),(0,[z687,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z688,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z117,z50,z5,z6]),(0,[z0,z1,z2,z106,z17,z5,z6]),(0,[z0,z1,z79,z3,z179,z5,z6]),(0,[z0,z1,z2,z3,z5,z118,z6])],[(0,[z0,z1,z2,z3,z5,z689,z6]),(0,[z0,z1,z2,z3,z690,z5,z6])],[(0,[z55,z1,z2,z101,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z94]),(0,[z691,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z118,z6,z100])],[(0,[z44,z148,z1,z2,z3,z5,z6]),(0,[z692,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z168,z3,z5,z6]),(0,[z0,z1,z693,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z97,z6,z24])],[(0,[z694,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z695,z3,z5,z6]),(0,[z0,z1,z2,z106,z3,z5,z6]),(0,[z696,z0,z1,z2,z3,z5,z6])],[(0,[z55,z0,z1,z2,z62,z5,z6]),(1,[z0,z1,z2,z3,z5,z419]),(0,[z55,z1,z2,z114,z3,z5,z6]),(0,[z0,z1,z149,z3,z5,z23,z6]),(0,[z697,z0,z1,z2,z3,z5,z6]),(0,[z0,z698,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z699,z6])],[(0,[z700,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z701,z5,z6]),(0,[z0,z1,z2,z3,z5,z702,z6]),(0,[z0,z1,z2,z703,z3,z5,z6]),(0,[z704,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z482]),(0,[z705,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z82,z6,z80])],[(0,[z0,z1,z2,z3,z5,z706,z6]),(0,[z0,z1,z2,z3,z5,z6,z80])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z490,z1,z149,z3,z5,z6]),(0,[z523,z1,z2,z3,z5,z138]),(0,[z0,z1,z307,z72,z5,z6])],[(0,[z0,z1,z2,z3,z707,z6]),(0,[z341,z1,z149,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z708])],[(0,[z0,z1,z2,z3,z709,z6]),(0,[z12,z1,z2,z62,z5,z6]),(0,[z710,z0,z1,z3,z5,z6]),(0,[z0,z31,z3,z317,z5,z6])],[(0,[z711,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z712]),(0,[z0,z1,z2,z3,z97,z713])],[(0,[z0,z1,z714,z3,z5,z6]),(0,[z0,z1,z2,z174,z5,z6])],[(0,[z715,z1,z2,z3,z5,z6]),(0,[z0,z716,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z713,z24])],[(0,[z0,z1,z2,z3,z717,z6]),(0,[z0,z1,z2,z718,z5,z6]),(0,[z59,z0,z2,z317,z5,z6])],[(0,[z0,z1,z2,z3,z5,z719]),(0,[z0,z1,z2,z720,z5,z6]),(0,[z0,z1,z721,z3,z5,z6]),(0,[z0,z722,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z217,z5,z419]),(0,[z0,z31,z50,z17,z5,z6]),(0,[z185,z0,z1,z2,z281,z24])],[(0,[z0,z1,z2,z3,z5,z723]),(0,[z0,z1,z210,z3,z43,z6]),(0,[z724,z1,z2,z3,z5,z6]),(0,[z471,z1,z2,z5,z6,z196])],[(0,[z55,z210,z101,z3,z5,z6]),(0,[z0,z1,z725,z3,z5,z6]),(0,[z0,z726,z2,z3,z5,z6])],[(1,[z0,z2,z3,z727,z6]),(0,[z0,z233,z2,z3,z5,z521]),(0,[z107,z0,z2,z3,z5,z108]),(0,[z0,z1,z16,z728,z5,z6]),(0,[z33,z0,z1,z3,z23,z6]),(0,[z35,z0,z1,z3,z5,z729])],[(0,[z0,z1,z2,z3,z730,z6]),(0,[z0,z89,z3,z17,z5,z6]),(0,[z731,z1,z2,z3,z5,z6])],[(0,[z0,z1,z732,z3,z5,z6]),(0,[z0,z1,z2,z3,z733,z6]),(0,[z11,z1,z2,z734,z5,z6])],[(0,[z1,z2,z3,z95,z5,z64]),(0,[z12,z1,z2,z95,z5,z64]),(0,[z57,z1,z58,z3,z129,z6])],[(0,[z0,z1,z2,z5,z6,z196]),(0,[z0,z1,z79,z3,z179,z6])]],
   [[(0,[z0,z1,z273,z3,z5,z284]),(0,[z119,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z6,z735]),(0,[z0,z1,z2,z736,z5,z6])],[(0,[z0,z1,z2,z3,z6,z737]),(0,[z738,z1,z2,z3,z5,z6])],[(0,[z1,z2,z739,z3,z5,z6]),(0,[z740,z1,z2,z3,z5,z6]),(0,[z0,z1,z89,z17,z5,z6]),(0,[z0,z741,z2,z3,z5,z6]),(0,[z185,z0,z1,z2,z3,z24])],[(0,[z44,z1,z2,z3,z5,z419]),(0,[z633,z1,z149,z3,z5,z6]),(0,[z534,z1,z2,z3,z69,z6]),(0,[z742,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z743]),(0,[z0,z1,z2,z3,z5,z744]),(0,[z112,z255,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z745]),(0,[z0,z1,z746,z3,z5,z6]),(0,[z0,z1,z2,z217,z43,z6]),(0,[z0,z1,z2,z3,z747,z6])],[(0,[z0,z1,z2,z3,z43,z284]),(0,[z263,z1,z2,z114,z5,z6]),(0,[z75,z0,z2,z3,z727,z6]),(0,[z0,z1,z2,z748,z5,z6]),(0,[z112,z1,z2,z383,z5,z6]),(1,[z0,z1,z2,z3,z713])],[(0,[z57,z1,z2,z3,z129,z6]),(1,[z1,z2,z39,z5,z138]),(0,[z30,z0,z1,z14,z5,z6]),(0,[z749,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z467,z3,z179,z6]),(0,[z0,z1,z2,z3,z750,z6]),(0,[z0,z1,z2,z751,z5,z6]),(0,[z0,z1,z2,z218,z5,z6]),(1,[z119,z1,z2,z5,z100])],[(0,[z0,z1,z752,z3,z5,z6]),(0,[z0,z1,z81,z3,z5,z82]),(0,[z0,z1,z2,z753,z118,z6])],[(0,[z0,z1,z754,z3,z5,z6]),(0,[z1,z2,z223,z3,z5,z6]),(0,[z0,z755,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z756,z6]),(0,[z1,z2,z170,z3,z129,z6]),(0,[z0,z1,z757,z3,z5,z6]),(0,[z0,z758,z2,z3,z5,z6]),(0,[z119,z1,z2,z3,z5,z100])],[(0,[z592,z0,z2,z3,z76,z6]),(0,[z0,z1,z2,z759,z5,z6])],[(0,[z25,z131,z2,z3,z5,z6]),(0,[z202,z277,z2,z3,z5,z6])],[(0,[z20,z1,z2,z3,z179,z6]),(0,[z0,z1,z2,z3,z175,z713])],[(0,[z44,z1,z2,z39,z5,z6]),(0,[z1,z2,z3,z5,z351,z719]),(0,[z33,z34,z1,z3,z23,z6]),(0,[z0,z1,z3,z23,z6,z491])]],
   [[(0,[z0,z1,z2,z62,z186,z6]),(0,[z55,z2,z101,z3,z186,z6]),(0,[z1,z2,z734,z95,z5,z6]),(0,[z760,z1,z2,z3,z5,z6]),(0,[z185,z0,z1,z299,z3,z24])],[(0,[z142,z277,z2,z3,z5,z6])],[(0,[z761,z0,z115,z3,z5,z6]),(0,[z762,z0,z1,z2,z3,z6]),(0,[z763,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z175,z272])],[(0,[z0,z1,z165,z17,z5,z6]),(0,[z0,z1,z2,z764,z5,z6]),(0,[z765,z1,z2,z3,z5,z6])],[(1,[z1,z2,z3,z766,z6]),(0,[z1,z2,z3,z5,z6,z767]),(0,[z0,z1,z2,z768,z5,z6]),(0,[z0,z1,z2,z769,z5,z6])],[(0,[z0,z1,z2,z3,z5,z770]),(0,[z0,z1,z2,z771,z5,z6]),(0,[z0,z256,z2,z3,z5,z6]),(1,[z20,z1,z3,z23,z6])],[(0,[z0,z1,z2,z772,z5,z6]),(0,[z0,z1,z2,z383,z358,z6]),(0,[z422,z0,z1,z2,z5,z100])],[(0,[z258,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z773]),(0,[z0,z233,z2,z5,z137,z196])]],
   [[(0,[z44,z1,z2,z3,z5,z706])],[(0,[z0,z1,z307,z5,z6,z100]),(0,[z0,z52,z2,z774,z5,z6]),(0,[z0,z1,z16,z17,z5,z6])],[(0,[z20,z1,z2,z3,z5,z6]),(0,[z775,z1,z2,z3,z5,z6]),(0,[z258,z1,z2,z3,z5,z776]),(0,[z777,z1,z2,z3,z5,z6])],[(0,[z0,z1,z273,z3,z5,z6]),(0,[z1,z2,z778,z3,z5,z6]),(0,[z1,z170,z3,z5,z129,z6]),(0,[z1,z2,z3,z5,z6,z779])],[(0,[z0,z780,z2,z3,z5,z6]),(0,[z0,z1,z2,z281,z5,z6])],[(0,[z0,z781,z2,z3,z5,z6]),(0,[z0,z782,z2,z3,z5,z6]),(0,[z783,z1,z2,z3,z5,z6])],[(0,[z455,z60,z0,z3,z5,z6]),(0,[z697,z1,z2,z95,z5,z6]),(0,[z784,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z785,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z786,z6]),(0,[z0,z1,z2,z39,z5,z6]),(0,[z787,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z788])],[(0,[z0,z1,z2,z3,z43,z6]),(0,[z140,z0,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z419,z138])],[(0,[z0,z1,z2,z3,z5,z64]),(0,[z0,z1,z641,z117,z5,z6]),(0,[z0,z789,z2,z3,z5,z6]),(0,[z0,z1,z299,z3,z5,z6])],[(0,[z0,z1,z210,z62,z5,z6]),(0,[z790,z0,z1,z2,z5,z6]),(0,[z513,z1,z2,z3,z5,z138]),(0,[z0,z1,z3,z5,z791,z6]),(0,[z185,z0,z1,z221,z3,z24])],[(0,[z0,z1,z149,z3,z328,z6]),(0,[z44,z1,z2,z3,z5,z427])],[(0,[z1,z2,z62,z5,z6,z138]),(0,[z0,z1,z2,z3,z5,z792]),(0,[z83,z1,z2,z3,z5,z719]),(0,[z1,z2,z3,z5,z719,z6]),(1,[z761,z0,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z793]),(0,[z794,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z86,z753,z6])],[(0,[z34,z1,z2,z3,z5,z6]),(0,[z0,z1,z79,z3,z791,z6])]],
   [[(0,[z0,z795,z2,z3,z5,z6]),(1,[z0,z2,z774,z5,z6]),(0,[z1,z2,z168,z5,z6,z482]),(0,[z119,z1,z2,z5,z6,z100]),(0,[z0,z277,z2,z218,z5,z6])],[(0,[z0,z277,z221,z3,z5,z6]),(0,[z796,z1,z2,z3,z5,z6])],[],[(0,[z1,z2,z3,z186,z6,z138]),(0,[z0,z1,z2,z797,z5,z6]),(0,[z1,z2,z3,z5,z798,z6])],[(0,[z0,z1,z2,z3,z799,z6]),(0,[z0,z1,z2,z800,z5,z6]),(0,[z471,z1,z2,z3,z5,z138]),(0,[z0,z52,z2,z50,z5,z6]),(0,[z0,z1,z801,z3,z5,z6])],[(0,[z112,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z802,z5,z6]),(0,[z0,z2,z3,z5,z803,z6]),(1,[z1,z170,z3,z129,z6]),(0,[z0,z131,z2,z174,z5,z6]),(0,[z804,z1,z2,z3,z5,z6])],[(0,[z207,z0,z2,z3,z5,z108]),(0,[z1,z2,z3,z5,z6,z805]),(0,[z806,z1,z2,z3,z5,z6]),(0,[z30,z0,z1,z117,z5,z6]),(0,[z0,z807,z2,z3,z5,z6])],[(0,[z697,z0,z1,z2,z5,z100]),(0,[z35,z0,z1,z3,z354,z80])]],
   [[(0,[z55,z2,z101,z217,z5,z6]),(0,[z0,z1,z808,z3,z5,z6]),(0,[z202,z1,z2,z3,z5,z6]),(0,[z471,z1,z2,z3,z5,z351]),(0,[z35,z0,z1,z3,z358,z80]),(0,[z809,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z62,z5,z284]),(0,[z55,z2,z101,z3,z5,z284]),(0,[z0,z1,z2,z159,z753,z6])],[(0,[z0,z1,z810,z2,z5,z6]),(0,[z0,z1,z2,z5,z811,z6]),(0,[z812,z1,z2,z3,z5,z6])],[(0,[z0,z1,z79,z3,z580,z6]),(0,[z0,z1,z2,z3,z5,z729]),(0,[z0,z1,z813,z3,z5,z6])],[(0,[z142,z1,z2,z3,z5,z6]),(0,[z1,z2,z39,z5,z6,z138]),(1,[z0,z31,z317,z5,z6]),(0,[z0,z1,z81,z3,z5,z729])],[(0,[z0,z1,z814,z3,z5,z6]),(1,[z0,z307,z50,z5,z6]),(0,[z0,z2,z774,z3,z5,z6]),(0,[z0,z1,z2,z72,z5,z400]),(0,[z815,z1,z2,z3,z5,z6])],[(0,[z0,z1,z816,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z817])],[(0,[z105,z0,z2,z5,z6,z378]),(0,[z0,z418,z2,z106,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z818,z6]),(0,[z0,z1,z2,z819,z5,z6]),(0,[z0,z1,z2,z3,z820,z6])],[(0,[z0,z1,z2,z821,z5,z6]),(0,[z0,z1,z170,z3,z69,z6]),(0,[z0,z1,z2,z3,z753,z6])],[(0,[z822,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z823])],[(0,[z0,z1,z2,z3,z824,z6]),(0,[z44,z1,z2,z62,z5,z6])],[(0,[z0,z277,z2,z281,z5,z6])],[(0,[z0,z1,z2,z3,z825,z6]),(0,[z826,z0,z1,z3,z5,z6]),(0,[z35,z0,z1,z383,z5,z80])],[(0,[z0,z1,z2,z827,z5,z6]),(0,[z0,z1,z2,z3,z43,z419]),(0,[z0,z1,z2,z5,z6,z828]),(0,[z0,z1,z2,z3,z829,z6])],[(0,[z830,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z5,z831,z6]),(0,[z599,z1,z149,z3,z5,z6]),(0,[z0,z1,z2,z832,z5,z6]),(0,[z0,z1,z2,z3,z5,z833])],[(0,[z105,z0,z2,z398,z5,z6])],[(0,[z0,z1,z2,z3,z834,z6]),(0,[z0,z1,z273,z217,z5,z6]),(0,[z0,z1,z2,z3,z835,z6]),(0,[z0,z1,z2,z734,z5,z6]),(0,[z20,z1,z2,z3,z23,z6]),(0,[z0,z1,z2,z836,z5,z6]),(0,[z0,z837,z2,z3,z5,z6]),(0,[z119,z1,z2,z72,z5,z6])],[(0,[z0,z684,z2,z3,z128,z6]),(0,[z60,z761,z0,z3,z5,z6]),(0,[z838,z1,z2,z3,z5,z6]),(0,[z839,z1,z2,z3,z5,z6]),(0,[z0,z277,z299,z3,z5,z6])],[(0,[z0,z2,z3,z5,z6,z840]),(0,[z1,z2,z3,z39,z5,z138]),(0,[z0,z1,z2,z841,z5,z6]),(0,[z842,z1,z2,z3,z5,z6])],[(0,[z0,z1,z843,z3,z5,z6]),(0,[z0,z1,z2,z844,z5,z6])],[(0,[z0,z1,z2,z845,z5,z6])],[(1,[z0,z1,z3,z791,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z846])],[(0,[z847,z0,z2,z3,z5,z6]),(0,[z71,z119,z1,z2,z5,z100])],[(0,[z0,z1,z848,z3,z5,z6]),(0,[z849,z1,z2,z3,z5,z6])],[(0,[z289,z0,z1,z2,z118,z6])],[(0,[z0,z1,z2,z62,z5,z6]),(0,[z55,z2,z101,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z850]),(0,[z0,z1,z221,z3,z5,z6])],[(0,[z0,z1,z2,z851,z5,z6]),(0,[z11,z1,z2,z397,z5,z6]),(0,[z0,z115,z31,z317,z5,z6])],[(0,[z0,z1,z2,z852,z5,z6]),(0,[z0,z1,z2,z3,z5,z853]),(0,[z44,z1,z2,z3,z5,z345]),(0,[z0,z1,z2,z854,z5,z6]),(0,[z35,z0,z255,z3,z5,z80])],[(0,[z0,z1,z855,z3,z5,z6]),(0,[z0,z1,z2,z728,z5,z6]),(0,[z35,z0,z131,z3,z5,z80])]],
   [[(0,[z0,z1,z210,z3,z186,z6])],[(0,[z856,z0,z1,z3,z5,z6]),(0,[z0,z16,z89,z17,z5,z6]),(0,[z0,z1,z2,z5,z6,z857])],[(0,[z431,z1,z47,z3,z5,z6]),(0,[z0,z1,z2,z3,z858,z6]),(0,[z0,z859,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z860,z6]),(0,[z0,z1,z2,z3,z861,z6]),(0,[z0,z1,z245,z17,z5,z6])],[(0,[z0,z1,z2,z862,z5,z6]),(0,[z0,z1,z2,z5,z351,z196]),(0,[z0,z1,z863,z3,z5,z6])],[(0,[z0,z1,z864,z3,z5,z6]),(0,[z1,z2,z865,z3,z5,z6]),(0,[z0,z866,z2,z3,z5,z6]),(0,[z0,z1,z2,z867,z5,z6])],[(0,[z46,z1,z47,z3,z5,z6]),(0,[z0,z255,z2,z3,z354,z6])],[(0,[z435,z0,z31,z3,z5,z6]),(0,[z0,z2,z3,z128,z727,z6]),(1,[z0,z89,z17,z5,z6]),(0,[z0,z255,z2,z3,z358,z6])]],
   [[(0,[z0,z1,z868,z3,z5,z6]),(0,[z0,z1,z2,z95,z5,z64]),(0,[z357,z1,z2,z3,z69,z6]),(0,[z51,z0,z1,z3,z5,z6]),(0,[z761,z0,z1,z3,z5,z6]),(0,[z0,z1,z2,z383,z354,z6])],[(0,[z0,z111,z31,z3,z5,z6])],[(0,[z0,z307,z3,z50,z5,z6])],[(0,[z1,z2,z5,z6,z482,z196])],[(0,[z0,z1,z2,z217,z186,z6]),(0,[z25,z1,z2,z3,z354,z6])],[(0,[z0,z1,z2,z3,z186,z284]),(0,[z46,z1,z301,z3,z5,z6]),(0,[z869,z0,z2,z3,z5,z6]),(0,[z25,z1,z2,z3,z358,z6])],[],[(0,[z46,z1,z506,z3,z5,z6]),(0,[z337,z0,z2,z3,z5,z108]),(0,[z0,z1,z2,z870,z5,z6]),(0,[z0,z1,z2,z3,z871,z6]),(0,[z471,z1,z2,z168,z5,z6]),(0,[z85,z0,z1,z2,z118,z6])]],
   [[(0,[z127,z1,z2,z95,z5,z6]),(1,[z1,z2,z3,z5,z719])],[(0,[z83,z1,z2,z3,z5,z138]),(0,[z0,z1,z3,z179,z791,z6])],[(0,[z366,z0,z1,z3,z23,z6]),(0,[z60,z0,z321,z3,z5,z6])],[(0,[z584,z1,z2,z3,z129,z6]),(1,[z0,z1,z2,z753,z6])],[(0,[z0,z1,z872,z3,z5,z6]),(0,[z2,z778,z101,z3,z5,z6]),(0,[z0,z1,z2,z873,z5,z6]),(0,[z0,z1,z2,z874,z5,z6]),(0,[z502,z1,z2,z3,z5,z138]),(0,[z1,z2,z3,z5,z6,z875]),(0,[z0,z1,z2,z876,z5,z6]),(0,[z173,z0,z1,z3,z23,z6]),(0,[z0,z255,z2,z383,z5,z6]),(0,[z35,z0,z1,z3,z5,z80])],[(0,[z0,z1,z2,z877,z5,z6]),(0,[z0,z1,z2,z878,z5,z6]),(0,[z0,z1,z2,z879,z5,z6]),(0,[z0,z1,z880,z3,z5,z6]),(0,[z660,z1,z2,z3,z5,z351]),(0,[z881,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z168,z5,z6]),(0,[z0,z882,z2,z3,z5,z6]),(0,[z883,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z884,z5,z6]),(0,[z112,z131,z2,z3,z5,z6])],[(0,[z44,z1,z2,z3,z186,z6]),(0,[z1,z149,z3,z129,z23,z6]),(0,[z0,z1,z394,z3,z179,z6]),(0,[z0,z1,z299,z3,z6,z24])]],
   [[(0,[z44,z1,z2,z3,z5,z351]),(0,[z0,z115,z31,z3,z5,z6]),(0,[z105,z0,z2,z106,z5,z6]),(0,[z885,z0,z1,z3,z5,z6]),(0,[z595,z0,z1,z3,z23,z6])],[(0,[z0,z1,z2,z62,z5,z419]),(0,[z55,z2,z101,z3,z5,z419]),(0,[z0,z52,z307,z50,z5,z6]),(0,[z0,z1,z2,z5,z6,z886])],[(0,[z25,z1,z2,z383,z5,z6])],[(0,[z471,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z887]),(0,[z0,z888,z2,z3,z5,z6]),(0,[z185,z142,z1,z2,z3,z24])],[(0,[z0,z1,z81,z3,z5,z41]),(0,[z0,z1,z2,z889,z5,z6]),(0,[z35,z112,z1,z3,z5,z80])],[(0,[z46,z1,z2,z3,z328,z6]),(0,[z366,z1,z2,z3,z129,z6]),(0,[z112,z1,z2,z174,z5,z6])],[(0,[z59,z0,z575,z3,z5,z6])],[]],
   [[(0,[z0,z1,z210,z217,z5,z6]),(0,[z0,z1,z2,z890,z5,z6]),(0,[z258,z1,z2,z114,z5,z6]),(0,[z0,z1,z2,z3,z5,z891])],[(0,[z0,z1,z210,z3,z5,z284]),(0,[z59,z761,z0,z3,z5,z6]),(0,[z892,z1,z2,z3,z5,z6]),(0,[z0,z1,z893,z3,z5,z6]),(0,[z894,z1,z2,z3,z5,z6]),(0,[z20,z1,z79,z3,z5,z6]),(0,[z0,z1,z2,z5,z753,z6])],[(0,[z0,z102,z2,z3,z252,z6]),(0,[z0,z1,z728,z17,z5,z6])],[(0,[z0,z1,z2,z3,z895,z6]),(0,[z0,z1,z2,z3,z5,z896])],[(0,[z0,z1,z2,z3,z5,z897]),(0,[z0,z1,z2,z898,z5,z6]),(0,[z401,z1,z2,z3,z5,z6]),(0,[z0,z1,z899,z3,z5,z6])],[(0,[z0,z900,z2,z3,z5,z6]),(0,[z1,z2,z95,z5,z6,z64]),(0,[z0,z1,z901,z3,z5,z6]),(0,[z105,z0,z307,z3,z5,z6]),(0,[z0,z902,z2,z3,z5,z6]),(0,[z903,z1,z2,z3,z5,z6])],[(0,[z904,z0,z1,z2,z5,z6]),(0,[z905,z1,z2,z3,z5,z6]),(0,[z0,z1,z728,z3,z5,z6]),(0,[z906,z1,z2,z3,z5,z6])],[(1,[z1,z865,z3,z5,z6]),(0,[z0,z102,z2,z3,z727,z6])]],
   [[(0,[z0,z1,z2,z3,z186,z6]),(0,[z0,z1,z2,z3,z907,z6])],[(0,[z761,z0,z2,z3,z5,z6])],[(0,[z0,z1,z908,z3,z5,z6]),(0,[z637,z1,z2,z3,z129,z6]),(0,[z0,z1,z2,z909,z5,z6]),(0,[z0,z1,z2,z910,z5,z6])],[(0,[z44,z1,z210,z3,z5,z6]),(0,[z0,z1,z273,z3,z5,z419]),(0,[z0,z1,z911,z3,z5,z6]),(0,[z0,z1,z2,z912,z5,z6])],[(0,[z0,z1,z2,z114,z5,z64]),(0,[z913,z1,z2,z3,z5,z6]),(0,[z0,z233,z2,z168,z5,z137])],[(0,[z0,z1,z2,z217,z5,z284]),(0,[z233,z2,z3,z5,z137,z482])],[(0,[z0,z1,z2,z3,z5,z914]),(0,[z0,z1,z2,z915,z5,z6])],[(0,[z0,z1,z2,z916,z5,z6]),(0,[z0,z2,z778,z3,z5,z6]),(0,[z55,z1,z2,z3,z5,z64]),(0,[z0,z917,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z354,z6])]],
   [[(0,[z0,z1,z2,z3,z358,z6]),(0,[z0,z1,z81,z3,z354,z6])],[(0,[z0,z1,z2,z3,z5,z918]),(0,[z45,z1,z2,z3,z5,z64]),(0,[z0,z1,z170,z3,z129,z6]),(0,[z687,z0,z2,z3,z76,z6])],[(0,[z0,z404,z31,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z919]),(0,[z471,z233,z2,z3,z5,z137]),(0,[z185,z0,z256,z2,z3,z24])],[(0,[z0,z1,z170,z3,z5,z6]),(0,[z148,z1,z2,z3,z261,z6])],[(0,[z0,z920,z2,z3,z5,z6]),(0,[z202,z1,z2,z218,z5,z6])],[(0,[z11,z1,z2,z114,z5,z6]),(0,[z401,z71,z1,z2,z5,z100])],[(0,[z0,z1,z2,z921,z5,z6]),(0,[z922,z1,z2,z3,z5,z6]),(0,[z140,z0,z16,z17,z5,z6])],[(0,[z329,z1,z2,z3,z129,z6]),(0,[z0,z923,z2,z3,z5,z6]),(0,[z924,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z273,z3,z43,z6]),(0,[z925,z1,z2,z3,z5,z6]),(0,[z0,z233,z2,z3,z5,z137]),(0,[z142,z1,z2,z218,z5,z6])],[(0,[z524,z1,z149,z3,z5,z6]),(0,[z0,z525,z2,z50,z5,z6]),(0,[z1,z2,z3,z5,z766,z6]),(0,[z0,z1,z926,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z712]),(0,[z927,z1,z2,z3,z5,z6])],[(0,[z189,z1,z149,z3,z5,z6]),(0,[z189,z1,z865,z3,z5,z6]),(0,[z0,z1,z2,z928,z5,z6])],[(0,[z0,z255,z2,z3,z5,z6]),(0,[z551,z0,z1,z117,z5,z6])],[(0,[z0,z1,z210,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z929]),(0,[z0,z930,z2,z3,z5,z6])],[(0,[z0,z1,z2,z383,z5,z6]),(0,[z0,z1,z2,z3,z5,z713])],[(0,[z0,z1,z2,z3,z931,z6]),(0,[z0,z932,z2,z3,z5,z6]),(1,[z1,z149,z3,z328,z6]),(0,[z0,z1,z2,z933,z5,z6]),(0,[z934,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z935]),(0,[z1,z149,z3,z5,z328,z6]),(0,[z12,z1,z2,z95,z5,z6]),(0,[z258,z1,z2,z95,z5,z6]),(0,[z148,z1,z170,z3,z5,z6]),(0,[z0,z115,z31,z232,z5,z6]),(0,[z0,z1,z936,z3,z5,z6]),(0,[z0,z1,z2,z3,z937,z6])]],
   [[(0,[z0,z1,z2,z3,z938,z6])],[(0,[z25,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z939,z5,z6]),(0,[z0,z277,z2,z3,z5,z6]),(0,[z0,z1,z940,z3,z5,z6]),(0,[z0,z1,z3,z5,z729,z80]),(0,[z202,z256,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z941,z6]),(0,[z683,z1,z2,z95,z5,z6]),(0,[z0,z1,z2,z5,z833,z100])],[(0,[z0,z1,z2,z3,z942,z6]),(0,[z0,z1,z2,z5,z6,z943])],[(0,[z0,z1,z2,z944,z5,z6]),(0,[z0,z233,z2,z3,z5,z712])],[(0,[z0,z1,z2,z3,z186,z419]),(0,[z0,z1,z2,z945,z5,z6]),(0,[z142,z256,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z946]),(0,[z20,z1,z3,z5,z23,z6]),(0,[z0,z947,z2,z3,z5,z6])],[(0,[z948,z1,z2,z3,z5,z6]),(0,[z0,z1,z949,z3,z5,z6]),(0,[z0,z1,z950,z3,z5,z6]),(0,[z951,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z217,z5,z6]),(0,[z1,z2,z3,z5,z952,z6]),(0,[z202,z1,z2,z281,z5,z6])],[(0,[z0,z1,z2,z3,z5,z284]),(0,[z0,z1,z2,z953,z5,z6]),(0,[z0,z1,z2,z954,z5,z6]),(0,[z0,z1,z2,z317,z5,z6]),(0,[z1,z2,z3,z5,z6,z955])],[(0,[z105,z0,z2,z774,z5,z6])],[(0,[z0,z1,z2,z956,z5,z6]),(0,[z0,z1,z2,z957,z5,z6]),(0,[z0,z1,z2,z5,z6,z958]),(0,[z0,z1,z307,z106,z5,z6]),(0,[z51,z0,z52,z50,z5,z6])],[(0,[z0,z1,z2,z3,z959,z6]),(0,[z0,z2,z960,z3,z5,z6]),(0,[z0,z1,z2,z5,z138,z196]),(0,[z961,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z72,z5,z474]),(0,[z142,z1,z2,z281,z5,z6]),(0,[z185,z0,z277,z2,z3,z24])],[(0,[z1,z865,z149,z3,z5,z6]),(0,[z258,z1,z2,z3,z5,z823])],[(0,[z0,z1,z2,z39,z5,z138])],[(0,[z0,z165,z2,z50,z5,z6]),(0,[z962,z1,z2,z3,z5,z6]),(0,[z0,z963,z2,z3,z5,z6]),(0,[z0,z119,z1,z2,z5,z100])]],
   [[(0,[z413,z1,z47,z3,z5,z6]),(0,[z1,z2,z3,z5,z964,z6]),(0,[z965,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z6,z833]),(0,[z0,z1,z221,z218,z5,z6])],[(0,[z0,z1,z2,z3,z5,z966]),(0,[z0,z1,z3,z354,z6,z80]),(0,[z0,z1,z2,z72,z5,z451])],[(0,[z0,z1,z2,z3,z967,z6]),(0,[z0,z1,z2,z39,z5,z351]),(0,[z968,z1,z2,z3,z5,z6]),(0,[z969,z1,z2,z3,z5,z6])],[(0,[z0,z2,z3,z5,z6,z970]),(0,[z971,z1,z2,z3,z5,z6]),(0,[z142,z1,z299,z3,z5,z6])],[(0,[z0,z1,z972,z3,z5,z6]),(0,[z35,z0,z1,z174,z5,z80]),(0,[z0,z1,z299,z3,z175,z6])],[(0,[z0,z1,z973,z3,z5,z6]),(0,[z507,z0,z1,z17,z5,z6])],[(0,[z597,z0,z2,z106,z5,z6]),(0,[z0,z1,z974,z3,z5,z6]),(0,[z59,z508,z0,z3,z5,z6]),(0,[z0,z1,z2,z3,z727,z6]),(0,[z975,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z6,z976])]],
   [[(0,[z0,z1,z2,z3,z5,z977]),(0,[z0,z2,z106,z774,z5,z6])],[(0,[z0,z1,z210,z3,z5,z419]),(0,[z127,z1,z2,z3,z5,z138]),(0,[z0,z102,z2,z3,z128,z6]),(0,[z978,z1,z2,z3,z5,z6])],[(0,[z0,z2,z774,z50,z5,z6]),(1,[z0,z1,z3,z5,z729])],[(0,[z0,z1,z58,z3,z5,z6]),(1,[z1,z2,z734,z5,z6]),(0,[z0,z1,z2,z3,z766,z6]),(0,[z0,z1,z2,z3,z5,z979]),(0,[z0,z2,z3,z5,z712,z108]),(0,[z25,z255,z2,z3,z5,z6]),(0,[z71,z0,z1,z2,z5,z833]),(0,[z980,z0,z2,z3,z5,z6])],[(0,[z0,z20,z1,z3,z23,z6]),(0,[z0,z1,z2,z159,z690,z6]),(0,[z0,z256,z2,z218,z5,z6])],[(0,[z0,z1,z2,z5,z6,z981]),(0,[z982,z1,z2,z3,z5,z6]),(0,[z0,z983,z2,z3,z5,z6]),(0,[z984,z1,z2,z3,z5,z6]),(0,[z0,z256,z221,z3,z5,z6])],[(0,[z0,z1,z2,z3,z985,z6]),(0,[z1,z2,z95,z5,z138,z100]),(0,[z0,z1,z307,z3,z5,z6]),(0,[z986,z1,z2,z3,z5,z6]),(0,[z987,z1,z2,z3,z5,z6])],[(0,[z258,z1,z2,z62,z5,z6]),(0,[z1,z2,z149,z3,z328,z6]),(0,[z0,z1,z3,z5,z6,z729]),(0,[z0,z1,z2,z3,z175,z97])]],
   [[(0,[z46,z1,z865,z3,z5,z6]),(0,[z988,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z82,z729]),(0,[z0,z989,z2,z3,z5,z6])],[(0,[z143,z0,z1,z3,z23,z6])],[(0,[z55,z273,z101,z3,z5,z6]),(0,[z990,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z991,z5,z6]),(0,[z0,z1,z273,z62,z5,z6]),(0,[z0,z992,z2,z3,z5,z6]),(0,[z0,z993,z2,z3,z5,z6]),(0,[z994,z0,z1,z3,z5,z6]),(0,[z995,z0,z1,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z996,z1,z2,z3,z5,z6]),(0,[z0,z1,z221,z281,z5,z6])],[(0,[z112,z1,z2,z3,z354,z6]),(0,[z0,z1,z2,z3,z6,z713])],[(0,[z997,z0,z2,z3,z5,z6]),(0,[z112,z1,z2,z3,z358,z6])],[(0,[z0,z1,z2,z3,z998,z6]),(0,[z1,z47,z865,z3,z5,z6]),(0,[z148,z1,z2,z3,z766,z6]),(0,[z0,z1,z2,z3,z5,z776]),(0,[z999,z1,z2,z3,z5,z6])]],
   [[(0,[z523,z0,z1,z2,z5,z100]),(0,[z0,z1,z2,z3,z1000,z6]),(0,[z0,z131,z2,z3,z354,z6])],[(0,[z0,z1,z2,z62,z43,z6]),(0,[z55,z2,z101,z3,z43,z6]),(0,[z148,z1,z2,z3,z69,z6]),(0,[z0,z1,z2,z3,z1001,z6]),(0,[z0,z1,z3,z5,z1002,z6]),(0,[z0,z131,z2,z3,z358,z6])],[(0,[z0,z1003,z2,z3,z5,z6]),(0,[z0,z1,z2,z1004,z5,z6]),(0,[z0,z1,z2,z1005,z5,z6]),(0,[z0,z1,z299,z218,z5,z6]),(0,[z185,z0,z1,z2,z218,z24])],[(0,[z1006,z0,z2,z3,z5,z6]),(0,[z0,z1007,z2,z3,z5,z6])],[(0,[z1,z2,z3,z766,z129,z6]),(0,[z0,z1,z2,z1008,z5,z6]),(0,[z0,z1,z287,z17,z5,z6])],[(0,[z57,z1,z2,z3,z766,z6]),(0,[z0,z1,z1009,z3,z5,z6]),(0,[z0,z2,z3,z5,z137,z712]),(0,[z0,z1,z117,z728,z5,z6]),(0,[z33,z20,z1,z3,z23,z6]),(0,[z282,z0,z1,z3,z23,z6])],[(0,[z0,z13,z2,z3,z5,z137]),(0,[z0,z9,z2,z50,z5,z6]),(0,[z0,z1010,z2,z3,z5,z6])],[(0,[z0,z1,z1011,z3,z5,z6]),(0,[z0,z1012,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1013]),(0,[z0,z1014,z2,z3,z5,z6]),(0,[z761,z0,z31,z3,z5,z6]),(0,[z30,z0,z89,z3,z5,z6]),(0,[z0,z1,z2,z174,z354,z6]),(0,[z185,z0,z1,z2,z3,z713])]],
   [[(0,[z189,z1,z149,z3,z392,z6]),(0,[z0,z1,z2,z3,z1015,z6]),(0,[z1016,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z174,z358,z6]),(0,[z0,z256,z2,z281,z5,z6])],[(0,[z0,z1,z2,z1017,z5,z6]),(1,[z1,z2,z95,z5,z64])],[(0,[z52,z2,z223,z50,z5,z6])],[(0,[z0,z1,z1018,z3,z5,z6]),(0,[z1019,z1,z2,z3,z5,z6])],[(0,[z107,z0,z2,z3,z5,z712]),(0,[z0,z1,z3,z791,z23,z6]),(0,[z156,z0,z1,z2,z3,z24]),(0,[z119,z1,z2,z3,z5,z120])],[(0,[z486,z1,z2,z114,z5,z6])],[(0,[z0,z89,z2,z117,z5,z6]),(1,[z0,z1,z728,z5,z6]),(0,[z0,z131,z2,z383,z5,z6]),(0,[z0,z1,z1020,z3,z5,z6]),(0,[z0,z1,z1021,z3,z5,z6])],[(0,[z0,z1,z1022,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1023]),(0,[z0,z256,z299,z3,z5,z6])]],
   [[(0,[z0,z1,z1024,z3,z5,z6]),(0,[z0,z1,z2,z3,z1025,z6]),(0,[z202,z1,z221,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1026,z6]),(0,[z55,z164,z2,z3,z5,z6]),(0,[z0,z1,z79,z3,z618,z6])],[(0,[z0,z1,z1027,z3,z5,z6]),(0,[z0,z1,z2,z1028,z5,z6]),(0,[z0,z1,z2,z1029,z5,z6]),(0,[z1030,z1,z2,z3,z5,z6])],[(0,[z471,z1,z2,z3,z5,z419]),(0,[z0,z1,z2,z3,z328,z6]),(0,[z0,z1,z47,z3,z328,z6]),(0,[z0,z1,z865,z3,z5,z6]),(0,[z0,z255,z2,z174,z5,z6])],[(0,[z0,z1,z2,z1031,z5,z6]),(0,[z490,z0,z1,z3,z23,z6]),(0,[z142,z1,z221,z3,z5,z6])],[(0,[z83,z1,z2,z39,z5,z138]),(0,[z0,z2,z31,z317,z5,z6]),(0,[z0,z1,z2,z1032,z5,z6]),(0,[z0,z1,z1033,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z94]),(0,[z0,z2,z307,z50,z5,z6]),(0,[z35,z25,z1,z3,z5,z80]),(0,[z0,z1,z299,z281,z5,z6])],[]],
   [[(0,[z0,z233,z2,z3,z5,z171]),(0,[z0,z1,z2,z3,z791,z6])],[(0,[z0,z1,z2,z3,z5,z419]),(0,[z0,z1,z2,z3,z1034,z6]),(0,[z0,z1,z2,z1035,z5,z6]),(0,[z156,z0,z1,z3,z5,z80]),(0,[z25,z1,z2,z174,z5,z6])],[(0,[z0,z1,z1036,z3,z5,z6]),(0,[z0,z1,z1037,z3,z5,z6]),(0,[z148,z1,z2,z3,z123,z6]),(0,[z0,z9,z31,z3,z5,z6]),(0,[z1038,z1,z2,z3,z5,z6]),(0,[z258,z52,z2,z50,z5,z6])],[(0,[z0,z1,z1039,z3,z5,z6]),(0,[z0,z1,z2,z774,z5,z6])],[(0,[z0,z1040,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z372,z138]),(0,[z0,z1,z2,z3,z5,z1041])],[(0,[z0,z1,z2,z5,z6,z1042]),(0,[z0,z1043,z2,z3,z5,z6]),(0,[z57,z1,z170,z3,z129,z6]),(0,[z1044,z0,z1,z2,z3,z5])],[(0,[z67,z1,z2,z3,z5,z138])]],
   [[(0,[z341,z1,z2,z3,z129,z6]),(0,[z1045,z1,z2,z3,z5,z6])],[(0,[z547,z0,z2,z50,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1046]),(0,[z240,z1,z2,z3,z5,z138]),(0,[z0,z1,z2,z1047,z5,z6]),(0,[z1,z2,z114,z734,z5,z6]),(0,[z0,z1048,z2,z3,z5,z6])],[(0,[z55,z2,z778,z3,z5,z6]),(0,[z1,z2,z734,z3,z5,z6]),(0,[z0,z1,z2,z232,z5,z6]),(0,[z0,z287,z31,z3,z5,z6]),(0,[z1049,z1,z2,z3,z5,z6]),(0,[z85,z0,z1,z2,z753,z6])],[(0,[z0,z1,z1050,z3,z5,z6]),(0,[z83,z1,z2,z121,z5,z138])],[(0,[z0,z1,z2,z3,z5,z1051]),(0,[z0,z52,z2,z654,z5,z6]),(0,[z0,z1,z2,z1052,z5,z6])],[(0,[z11,z1,z2,z3,z5,z64]),(1,[z0,z2,z3,z5,z712])],[(0,[z0,z1,z273,z3,z186,z6]),(0,[z0,z1,z2,z3,z1053,z6]),(0,[z59,z60,z0,z3,z5,z6]),(0,[z0,z1,z31,z317,z5,z6])]],
   [[(0,[z0,z1,z307,z50,z5,z6]),(0,[z0,z89,z2,z17,z5,z6])],[(0,[z0,z1,z2,z1054,z5,z6])],[(0,[z0,z1,z1055,z3,z5,z6]),(0,[z0,z1,z2,z5,z621,z100]),(0,[z75,z0,z2,z3,z76,z6]),(0,[z77,z0,z2,z3,z5,z108]),(0,[z202,z1,z299,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1056,z6]),(0,[z229,z0,z1,z2,z5,z100])],[(0,[z1,z2,z114,z62,z5,z6]),(0,[z55,z2,z101,z62,z5,z6]),(0,[z0,z1,z2,z3,z5,z1057]),(0,[z1,z2,z3,z5,z6,z482]),(0,[z189,z1,z149,z3,z328,z6]),(0,[z0,z89,z2,z3,z5,z6]),(0,[z0,z1,z2,z1058,z5,z6])],[(0,[z0,z1,z2,z159,z86,z6])],[(0,[z1,z210,z3,z5,z6,z138]),(0,[z1,z2,z114,z73,z5,z6]),(0,[z44,z1,z2,z3,z5,z719]),(0,[z1059,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z1060,z5,z6]),(0,[z0,z1,z2,z3,z1061,z6]),(0,[z0,z1,z2,z1062,z5,z6]),(0,[z1,z2,z3,z5,z719,z138]),(0,[z0,z1,z2,z3,z5,z1063]),(0,[z0,z1,z1064,z3,z5,z6]),(0,[z0,z2,z3,z727,z76,z6]),(0,[z30,z0,z1,z728,z5,z6]),(0,[z71,z0,z1,z2,z5,z100])]],
   [[(0,[z12,z1,z2,z734,z5,z6]),(0,[z0,z2,z3,z5,z727,z6]),(0,[z1,z2,z1065,z3,z5,z6])],[(0,[z0,z1,z2,z1066,z5,z6])],[(0,[z0,z1,z2,z3,z392,z6]),(0,[z0,z1,z2,z3,z5,z1067]),(0,[z593,z0,z1,z2,z5,z100]),(0,[z60,z0,z1,z317,z5,z6])],[(0,[z0,z1,z1068,z3,z5,z6])],[(0,[z0,z1,z2,z121,z5,z6]),(0,[z12,z1,z2,z95,z5,z94]),(0,[z0,z1,z2,z1069,z5,z6]),(0,[z0,z1,z2,z3,z1070,z6])],[(0,[z0,z1,z2,z1071,z5,z6]),(0,[z0,z1,z2,z3,z5,z1072]),(0,[z0,z1,z2,z1073,z5,z6]),(0,[z0,z131,z2,z3,z5,z6]),(0,[z1074,z1,z2,z3,z5,z6])],[(0,[z55,z2,z26,z3,z5,z6]),(0,[z1,z2,z3,z69,z766,z6]),(0,[z1075,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z6,z1076]),(0,[z0,z1,z2,z1077,z5,z6]),(0,[z33,z0,z1,z3,z791,z6]),(0,[z185,z202,z1,z2,z3,z24])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 555) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 555).take 493) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1048)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [555, 493] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 152).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 152).take 104).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [152, 104] = true :=
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

end PEqualNP.Outside.L_meta_38049

theorem PEqualNP.Outside.L_meta_38049 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124200 * 2 ^ 32 + 4274845832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124200 * 2 ^ 32 + 4274845832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38049.solve