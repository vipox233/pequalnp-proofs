import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38861

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
  Nat.testBit (4276808936 * 2 ^ 32 + 4209680544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00082380b0282aac#64 ++ 0x2001047016050555#64 ++ 0xb819e781f078ffff#64 ++ 0xd7033cf03e0f1fff#64 : BitVec 256),
   (0x086288b65c636661#64 ++ 0x410c5116cb8c6ccc#64 ++ 0xe8e699fe7c676667#64 ++ 0xbd1cd33fcf8ceccc#64 : BitVec 256),
   (0x03051c0b05858551#64 ++ 0x8060a38160b0b0aa#64 ++ 0xbf071e0f8f8787ff#64 ++ 0x77e0e3c1f1f0f0ff#64 : BitVec 256),
   (0x15b81fd00ef80786#64 ++ 0x02b703fa01df00f0#64 ++ 0xd7f81ff00ff80786#64 ++ 0xfaff03fe01ff00f0#64 : BitVec 256),
   (0x06f7c0000b56d000#64 ++ 0x00def800016ada00#64 ++ 0xdfffe0000ffff805#64 ++ 0xfbfffc0001ffff00#64 : BitVec 256),
   (0x27dff76de0000000#64 ++ 0x04fbfeedbc000000#64 ++ 0xe7fffffff0000003#64 ++ 0xfcfffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 2]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [9, 8]⟩, ⟨.or, [10, 13]⟩, ⟨.and, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0xb8010601800087ff 0x570020c0300010ff

def z1 : W := mkw 0x00082380b0282aac 0x2001047016050555 0x0018e18070787800 0x80031c300e0f0f00

def z2 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0xbf071e0f8f8787ff 0x77e0e3c1f1f0f0ff

def z3 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0xdfffe0000ffff805 0xfbfffc0001ffff00

def z4 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xe8e699fe7c676667 0xbd1cd33fcf8ceccc

def z5 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xd7f81ff00ff80786 0xfaff03fe01ff00f0

def z6 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xe7fffffff0000003 0xfcfffffffe000000

def z7 : W := mkw 0x00082380b0282aac 0x2001047016050555 0xb819e781f078ffff 0xd7033cf03e0f1fff

def z8 : W := mkw 0x14b823d0ba782aae 0x2297047a174f0555 0x40f8e1f070787800 0x881f1c3e0e0f0f00

def z9 : W := mkw 0x15b83fd0bef82fae 0x22b707fa17df05f5 0xfff9fff1fff8ffff 0xffff3ffe3fff1fff

def z10 : W := mkw 0x004aa3a4f0282aac 0x200954749e050555 0xf8fffffff078ffff 0xff1ffffffe0f1fff

def z11 : W := mkw 0x00082300a008088c 0x2001046014010111 0xb019e781f018999b 0xd6033cf03e031333

def z12 : W := mkw 0x082008921c636661 0x41040112438c6ccc 0x080000000c676664 0x01000000018ceccc

def z13 : W := mkw 0x0ef7c8b65f77f661 0x41def916cbeefecc 0xfffff9fe7ffffe67 0xffffff3fcfffffcc

def z14 : W := mkw 0x2247e02de0000000 0x0448fc05bc000000 0x2007e00ff0000001 0x0400fc01fe000000

def z15 : W := mkw 0x0000000000000000 0x0000000000000000 0xb819e6018078ffff 0xd7033cc0300f1fff

def z16 : W := mkw 0x0000080204010441 0x0000010040802088 0xa806180e0c070667 0x3500c301c180e0cc

def z17 : W := mkw 0x21083749a0000000 0x042106e934000000 0x0000060180000000 0x000000c030000000

def z18 : W := mkw 0x002008900c600600 0x00040112018c00c0 0xc0e019f00c600606 0xb81c033e018c00c0

def z19 : W := mkw 0x04b000000a500000 0x00960000014a0000 0xd7f800000ff80004 0xfaff000001ff0000

def z20 : W := mkw 0x11081fd004a80786 0x022103fa009500f0 0x00001ff000000782 0x000003fe000000f0

def z21 : W := mkw 0x17ffdfd00ffed786 0x02fffbfa01ffdaf0 0xdffffff00fffff87 0xfbfffffe01fffff0

def z22 : W := mkw 0x01083f8bb4a92ffd 0xa02107f1769525ff 0x20001f8ff00007fa 0x040003f1fe0000ff

def z23 : W := mkw 0x06ffe380bb7efaac 0x20dffc70176fdf55 0xdfffe1807ffff805 0xfbfffc300fffff00

def z24 : W := mkw 0x2ffffffffc636661 0x45ffffffff8c6ccc 0xeffffffffc676667 0xfdffffffff8ceccc

def z25 : W := mkw 0x27dff76de1048000 0x04fbfeedbc209000 0xffffffffff878007 0xfffffffffff0f000

def z26 : W := mkw 0x279d7749a1848110 0x84f3aee934309022 0x1719660183808198 0x42e32cc030701033

def z27 : W := mkw 0x27dfff6fe5858551 0x84fbffedfcb0b0aa 0xffffffffff8787ff 0xfffffffffff0f0ff

def z28 : W := mkw 0x1000000002980186 0x0200000000530030 0x1000000003980180 0x0200000000730030

def z29 : W := mkw 0x15b01c500ed00502 0x02b6038a01da00a0 0x47e018700f800000 0x28fc030e01f00000

def z30 : W := mkw 0x00082380b0282aac 0x2001047016050555 0x20000781f00007fa 0x040000f03e0000ff

def z31 : W := mkw 0x04f2c0000a525000 0x009e5800014a4a00 0x40f8e00000787800 0x881f1c00000f0f00

def z32 : W := mkw 0x24dae364e0000000 0x049b5c6c9c000000 0xe0fef9fe70000003 0xbc1fdf3fce000000

def z33 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0x0706180e0f870000 0x20e0c301c1f0e000

def z34 : W := mkw 0x2108376de0000000 0x042106edbc000000 0xa019fffff0000003 0xd4033ffffe000000

def z35 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0x57f9e00003f8f800 0xcaff3c00007f1f00

def z36 : W := mkw 0x0000008010282aac 0x2000001002050555 0xb80106018078ffff 0x570020c0300f1fff

def z37 : W := mkw 0x086aabb6fc6b6eed 0x610d5576df8d6ddd 0xf8fffffffc7fffff 0xff1fffffff8fffff

def z38 : W := mkw 0x04b000000a500000 0x00960000014a0000 0x47e000000f800000 0x28fc000001f00000

def z39 : W := mkw 0x0247c00000000000 0x0048f80000000000 0x0007e00000000001 0x0000fc0000000000

def z40 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0e019f000000002 0xb81c033e00000000

def z41 : W := mkw 0x279d7749a0000000 0x04f3aee934000000 0x0719660180000000 0x40e32cc030000000

def z42 : W := mkw 0x24dae3e4f0282aac 0x249b5c7c9e050555 0x40f8e1f070787800 0x881f1c3e0e0f0f00

def z43 : W := mkw 0x0042802440000000 0x0008500488000000 0xe0e699fe70000003 0xbc1cd33fce000000

def z44 : W := mkw 0x0205200bb105a879 0xa040a4017620b50f 0x2807e00ff007f879 0x0500fc01fe00ff0f

def z45 : W := mkw 0x00002000b0002828 0x2000040016000505 0x2801e001f000f879 0x05003c003e001f0f

def z46 : W := mkw 0x030d3789b1acabbc 0xa061a6f136359577 0xbf19e781f3f8ffff 0xd7e33cf03e7f1fff

def z47 : W := mkw 0x11201c900ef80786 0x0224039201df00f0 0x97001e000ff80786 0x72e003c001ff00f0

def z48 : W := mkw 0x279d7749a0000000 0x04f3aee934000000 0xc7f97ff180000002 0xf8ff2ffe30000000

def z49 : W := mkw 0x0598174000000000 0x00b302e800000000 0xc7f81ff000000002 0xf8ff03fe00000000

def z50 : W := mkw 0x0247c0000106d000 0x0048f8000020da00 0x0006000000070000 0x0000c0000000e000

def z51 : W := mkw 0x07f7dc0b0fd7d551 0x80fefb8161fafaaa 0xfffffe0f8fffffff 0xffffffc1f1ffffff

def z52 : W := mkw 0x15b81fd20ef907c7 0x02b703fa41df20f8 0xfffe1ffe0fff07e7 0xffffc3ffc1ffe0fc

def z53 : W := mkw 0x030d1f8b05ad87d5 0x8061a3f160b5b0fa 0xbf1f1f8f8fff87ff 0xf7e3e3f1f1fff0ff

def z54 : W := mkw 0x00082380b0282aac 0x2001047016050555 0x1019e781f078f998 0xc2033cf03e0f1f33

def z55 : W := mkw 0x14b803d00a780286 0x0297007a014f0050 0x40f801f000780000 0x881f003e000f0000

def z56 : W := mkw 0x06f7c8020fd7d551 0x80def90041fafaaa 0xdfffe0000ffffffd 0xfbfffc0001ffffff

def z57 : W := mkw 0x0000000000000000 0x0000000000000000 0x9018000000780004 0xd2030000000f0000

def z58 : W := mkw 0x0008038000280284 0x0001007000050050 0x9018078000780786 0xd20300f0000f00f0

def z59 : W := mkw 0x224fe32de0000000 0x0449fc65bc000000 0xa01fe78ff0000003 0xd403fcf1fe000000

def z60 : W := mkw 0x27d7d46d40000000 0x04fafa8da8000000 0x47e6187e00000000 0x28fcc30fc0000000

def z61 : W := mkw 0x01001c0004800500 0x00200380009000a0 0x97001e000f800786 0x72e003c001f000f0

def z62 : W := mkw 0x21083f6fe4810551 0x842107edfc9020aa 0x20001ffff00007fa 0x040003fffe0000ff

def z63 : W := mkw 0x002000000b56d000 0x00040000016ada00 0x180000000ffff804 0x0300000001ffff00

def z64 : W := mkw 0x06d7c00000000000 0x00daf80000000000 0xc7ffe00000000001 0xf8fffc0000000000

def z65 : W := mkw 0x27fff76deb56d000 0x04fffeedbd6ada00 0xfffffffffffff807 0xffffffffffffff00

def z66 : W := mkw 0x1dfa9ff65efb67e7 0x43bf53fecbdf6cfc 0xfffe9ffe7fff67e7 0xffffd3ffcfffecfc

def z67 : W := mkw 0x01001c0b04810551 0x80200381609020aa 0x20001e0f800007fa 0x040003c1f00000ff

def z68 : W := mkw 0x2ffff7fdf8626220 0x45fffeffbf0c4c44 0xe7fffffff0606003 0xfcfffffffe0c0c00

def z69 : W := mkw 0x35fafff4eef80786 0x06bf5ffe9ddf00f0 0xd7f8fff07ff80786 0xfaff1ffe0fff00f0

def z70 : W := mkw 0x2108376de0000000 0x042106edbc000000 0x20001ffff0000002 0x040003fffe000000

def z71 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xf8fff9fe7c7ffe67 0xff1fff3fcf8fffcc

def z72 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xdff9fff00ff8ff87 0xfbff3ffe01ff1ff0

def z73 : W := mkw 0x27dff7edf0282aac 0x24fbfefdbe050555 0xfffffffff078ffff 0xfffffffffe0f1fff

def z74 : W := mkw 0x27dff749a0000000 0x04fbfee934000000 0xc7ffe60180000001 0xf8fffcc030000000

def z75 : W := mkw 0x082008b65c612661 0x41040116cb8c24cc 0xe0e019fe7c600666 0xbc1c033fcf8c00cc

def z76 : W := mkw 0x07ffff8bbffffffd 0xa0fffff177ffffff 0xffffff8fffffffff 0xfffffff1ffffffff

def z77 : W := mkw 0x1dfabff6fefb6fef 0x63bf57fedfdf6dfd 0xffffffffffffffff 0xffffffffffffffff

def z78 : W := mkw 0x0000000000000000 0x0000000000000000 0x1019600000189800 0x42032c0000031300

def z79 : W := mkw 0x0695400003149000 0x00d2a80000629200 0x1719600003989800 0x42e32c0000731300

def z80 : W := mkw 0x09629cbf5ce36771 0xc12c5397eb9c6cee 0xe8e69ffffc6767ff 0xbd1cd3ffff8cecff

def z81 : W := mkw 0x01001c0004800500 0x00200380009000a0 0x00001e0000000782 0x000003c0000000f0

def z82 : W := mkw 0x04f2c0000b56d000 0x009e5800016ada00 0x58f8e0000ffff804 0x8b1f1c0001ffff00

def z83 : W := mkw 0x030d3f8bb5adaffd 0xa061a7f176b5b5ff 0xbf1fff8fffffffff 0xf7e3fff1ffffffff

def z84 : W := mkw 0x00002000a0000000 0x0000040014000000 0x2001e001f0000001 0x04003c003e000000

def z85 : W := mkw 0x15981f4006980586 0x02b303e800d300b0 0x97181e000f980786 0x72e303c001f300f0

def z86 : W := mkw 0x00082380a0280a8c 0x2001047014050151 0x9019678180789f9e 0xd2032cf0300f13f3

def z87 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0xffffe6018fffffff 0xfffffcc031ffffff

def z88 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0x47fee0000fff7800 0xa8ffdc0001ffef00

def z89 : W := mkw 0x06ffe300ab5ed88c 0x20dffc60156bdb11 0xdfffe6018ffff99d 0xfbfffcc031ffff33

def z90 : W := mkw 0x0000008000280284 0x0000001000050050 0x1000000000780784 0x02000000000f00f0

def z91 : W := mkw 0x0305140900000000 0x0060a28120000000 0xa7071e0f80000003 0x74e0e3c1f0000000

def z92 : W := mkw 0x102008100ed00502 0x0204010201da00a0 0x000000000f800000 0x0000000001f00000

def z93 : W := mkw 0x0062800008424000 0x000c500001084800 0xc8e680000c676005 0xb91cd000018cec00

def z94 : W := mkw 0x04f280000a524000 0x009e5000014a4800 0xdffe80000fff6005 0xfbffd00001ffec00

def z95 : W := mkw 0x0862a8b6fc636e69 0x610c5516df8c6dcd 0xe8e7f9fffc67fe7f 0xbd1cff3fff8cffcf

def z96 : W := mkw 0x086280b458626220 0x410c50168b0c4c44 0x40e081f070606000 0x881c103e0e0c0c00

def z97 : W := mkw 0x06f7c0244b56d000 0x00def804896ada00 0xfffff9fe7ffff807 0xffffff3fcfffff00

def z98 : W := mkw 0x00082300a008088c 0x2001046014010111 0x1019660180189998 0x42032cc030031333

def z99 : W := mkw 0x07f7dc0b0fd7d551 0x80fefb8161fafaaa 0x47e6180e0f870000 0x28fcc301c1f0e000

def z100 : W := mkw 0x1598174002980186 0x02b302e800530030 0xd7f81ff003980182 0xfaff03fe00730030

def z101 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0x40e699fe7c676000 0xa81cd33fcf8cec00

def z102 : W := mkw 0x102008900ef80786 0x0204011201df00f0 0x100000000ff80784 0x0200000001ff00f0

def z103 : W := mkw 0x0205400001049000 0x0040a80000209200 0x0001600000009800 0x00002c0000001300

def z104 : W := mkw 0x00082300a0000000 0x0001046014000000 0x20000781f0000002 0x040000f03e000000

def z105 : W := mkw 0x086288364c434441 0x410c5106c9886888 0x40e6187e0c070000 0x281cc30fc180e000

def z106 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0x48e6187e0c676664 0x291cc30fc18ceccc

def z107 : W := mkw 0x0000008010282aac 0x2000001002050555 0x180000000078fffc 0x03000000000f1fff

def z108 : W := mkw 0x006aa380b86a6aac 0x200d5470170d4d55 0xf8ffe781fc7fffff 0xff1ffcf03f8fffff

def z109 : W := mkw 0x1db81fd21efb67e7 0x43b703fa43df6cfc 0xdff81ff00fff67e6 0xfbff03fe01ffecfc

def z110 : W := mkw 0x06ffe380bb7efaac 0x20dffc70176fdf55 0xffffe781ffffffff 0xfffffcf03fffffff

def z111 : W := mkw 0x17ffdfd00ffed786 0x02fffbfa01ffdaf0 0xd7fe1ff00fff0786 0xfaffc3fe01ffe0f0

def z112 : W := mkw 0x0695400000000000 0x00d2a80000000000 0x0719600000000000 0x40e32c0000000000

def z113 : W := mkw 0x0000008010202220 0x0000001002040444 0x0800000000606664 0x01000000000c0ccc

def z114 : W := mkw 0x37fffffdeef80786 0x06ffffffbddf00f0 0xf7fffffffff80787 0xfeffffffffff00f0

def z115 : W := mkw 0x0a47c0265107f061 0x4148f804ca20fe0c 0x2807e00e7007f861 0x0500fc01ce00ff0c

def z116 : W := mkw 0x2fdff76ff0036061 0x45fbfeedfe006c0c 0xeffffffff0076063 0xfdfffffffe00ec0c

def z117 : W := mkw 0x17bd1fdb0ffd87d7 0x82f7a3fb61ffb0fa 0xffff1fff8fff87ff 0xffffe3fff1fff0ff

def z118 : W := mkw 0x15b83fd0bef82fae 0x22b707fa17df05f5 0xd7f8fff07ff87f86 0xfaff1ffe0fff0ff0

def z119 : W := mkw 0x086280b458626220 0x410c50168b0c4c44 0xe8e081f070606667 0x9d1c103e0e0c0ccc

def z120 : W := mkw 0x03053c0bb585ad79 0xa060a78176b0b5af 0xbf07fe0fff87ffff 0x77e0ffc1fff0ffff

def z121 : W := mkw 0x0000080205858551 0x8000010040b0b0aa 0x180000000f8787fc 0x0300000001f0f0ff

def z122 : W := mkw 0x0590144000000000 0x00b2028800000000 0x47e0187000000000 0x28fc030e00000000

def z123 : W := mkw 0x14b803d00a780286 0x0297007a014f0050 0xd7f801f00ff80004 0xfaff003e01ff0000

def z124 : W := mkw 0x0000088215adaffd 0xa000011042b5b5ff 0x180000000ffffffc 0x0300000001ffffff

def z125 : W := mkw 0x0042882644010441 0x00085104c8802088 0xe8e699fe7c070667 0xbd1cd33fcf80e0cc

def z126 : W := mkw 0x15b817400ad80186 0x02b702e8015b0030 0xd7f806000ff80184 0xfaff00c001ff0030

def z127 : W := mkw 0x19081ff654a927e7 0x432103feca9524fc 0x20001ffe700007e2 0x040003ffce0000fc

def z128 : W := mkw 0x15b01c500ed00502 0x02b6038a01da00a0 0xd7e01e700f800786 0x7afc03ce01f000f0

def z129 : W := mkw 0x27d7f46de0000000 0x04fafe8dbc000000 0x67e7f87ff0000001 0x2cfcff0ffe000000

def z130 : W := mkw 0x0000000000000000 0x0000000000000000 0x880600000c070005 0x3100c0000180e000

def z131 : W := mkw 0x0305140901848110 0x8060a28120309022 0xb7071e0f8380819b 0x76e0e3c1f0701033

def z132 : W := mkw 0x0842802650036061 0x41085004ca006c0c 0xe8e699fe70076063 0xbd1cd33fce00ec0c

def z133 : W := mkw 0x0247c0000106d000 0x0048f8000020da00 0x0807e0000007f801 0x0100fc000000ff00

def z134 : W := mkw 0x27dff76de008088c 0x24fbfeedbc010111 0xf7fffffff018999b 0xfefffffffe031333

def z135 : W := mkw 0x27dff76de106d000 0x04fbfeedbc20da00 0xeffffffff007f803 0xfdfffffffe00ff00

def z136 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0x2f07180f8f878079 0x25e0e301f1f0f00f

def z137 : W := mkw 0x27dff76de1848110 0x84fbfeedbc309022 0xf7fffffff380819b 0xfefffffffe701033

def z138 : W := mkw 0x00082300b00828ac 0x2001046016010515 0x3819e601f018f9f9 0x47033cc03e031f3f

def z139 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0x57ff60000f9f9800 0x6affec0001f3f300

def z140 : W := mkw 0x17ffffd0bffeffae 0x22fffffa17ffdff5 0xfffffff1ffffffff 0xfffffffe3fffffff

def z141 : W := mkw 0x0305140901848110 0x8060a28120309022 0x1701060183808198 0x42e020c030701033

def z142 : W := mkw 0x0205000b01058051 0x8040a0016020b00a 0x2807000f80078079 0x0500e001f000f00f

def z143 : W := mkw 0x00082380b0282aac 0x2001047016050555 0xa019e781f0787803 0xd4033cf03e0f0f00

def z144 : W := mkw 0x082008921f77f661 0x4104011243eefecc 0x180000000ffffe64 0x0300000001ffffcc

def z145 : W := mkw 0x01001c0b04810551 0x80200381609020aa 0x0000180e00000000 0x00000301c0000000

def z146 : W := mkw 0x0000000000000000 0x0000000000000000 0x9819e0000078f805 0xd3033c00000f1f00

def z147 : W := mkw 0x0000008010202220 0x0000001002040444 0xa800818070606667 0x950010300e0c0ccc

def z148 : W := mkw 0x1df29cf65ef36763 0x43be539ecbde6cec 0xefe699fe7fe76667 0xbdfcd33fcffceccc

def z149 : W := mkw 0x0020009008600200 0x00040012010c0040 0x40e001f000600000 0x881c003e000c0000

def z150 : W := mkw 0x0842882654036461 0x41085104ca806c8c 0xa806980e7c076667 0x3500d301cf80eccc

def z151 : W := mkw 0x27fff76de8424000 0x04fffeedbd084800 0xeffffffffc676007 0xfdffffffff8cec00

def z152 : W := mkw 0x04b008900e700600 0x0096011201ce00c0 0xd7f819f00ff80606 0xfaff033e01ff00c0

def z153 : W := mkw 0x0008038000280284 0x0001007000050050 0x9819e7800078ff87 0xd3033cf0000f1ff0

def z154 : W := mkw 0x159837c0b2b82bae 0x22b306f816570575 0xbf19e781f3f8ffff 0xd7e33cf03e7f1fff

def z155 : W := mkw 0x06b540000b56d000 0x00d6a800016ada00 0x1f1960000ffff804 0x43e32c0001ffff00

def z156 : W := mkw 0x020d238bb12daafd 0xa041a4717625b55f 0xb81fe78ff07fffff 0xd703fcf1fe0fffff

def z157 : W := mkw 0x214ab76de0000000 0x042956edbc000000 0xe0e69ffff0000003 0xbc1cd3fffe000000

def z158 : W := mkw 0x0267c0000b56d000 0x004cf800016ada00 0x1807e0000ffff805 0x0300fc0001ffff00

def z159 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0x47ff7e7f80000000 0x68ffefcff0000000

def z160 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0x4fe7e0000f87f801 0x29fcfc0001f0ff00

def z161 : W := mkw 0x00082300a008088c 0x2001046014010111 0xb819660180189fff 0x57032cc0300313ff

def z162 : W := mkw 0x03051c0905848510 0x8060a38120b090a2 0x97011e018f80879e 0x72e023c031f010f3

def z163 : W := mkw 0x20082364e0000000 0x0401046c9c000000 0x000001f070000000 0x0000003e0e000000

def z164 : W := mkw 0x00082380b0282aac 0x2001047016050555 0x9018e78070787f86 0xd2031cf00e0f0ff0

def z165 : W := mkw 0x086280b458626220 0x410c50168b0c4c44 0xe0e699fe70606003 0xbc1cd33fce0c0c00

def z166 : W := mkw 0x27d7d46d40000000 0x04fafa8da8000000 0xe7e699fe70000003 0xbcfcd33fce000000

def z167 : W := mkw 0x0205000001048000 0x0040a00000209000 0x9f0700000f878005 0x73e0e00001f0f000

def z168 : W := mkw 0x03479c2f45858551 0x8068f385e8b0b0aa 0xffe79fffff8787ff 0xfffcf3fffff0f0ff

def z169 : W := mkw 0x06dfe380b0282aac 0x20dbfc7016050555 0xffffe781f078ffff 0xfffffcf03e0f1fff

def z170 : W := mkw 0x086aabb6fc636661 0x410d5576df8c6ccc 0xe8fffffffc676667 0xfd1fffffff8ceccc

def z171 : W := mkw 0x2fdffffff4212661 0x45fbfffffe8424cc 0xe7fffffff0000663 0xfcfffffffe0000cc

def z172 : W := mkw 0x0b251c9b1de7e771 0xc164a39363bcfcee 0xbf071e0f8fe7e7ff 0x77e0e3c1f1fcfcff

def z173 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0x47e600000f870000 0x28fcc00001f0e000

def z174 : W := mkw 0x15b817d00a780286 0x02b702fa014f0050 0xc7f81ff000780002 0xf8ff03fe000f0000

def z175 : W := mkw 0x0042802440000000 0x0008500488000000 0x40e6187e00000000 0x281cc30fc0000000

def z176 : W := mkw 0x06d7c00003149000 0x00daf80000629200 0xd7ffe00003989801 0xfafffc0000731300

def z177 : W := mkw 0x0000080205858551 0x8000010040b0b0aa 0xb806180e0f8787ff 0x3700c301c1f0f0ff

def z178 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0xdfe700000f878005 0x7bfce00001f0f000

def z179 : W := mkw 0x11001c5004800502 0x0220038a009000a0 0x0000187000000000 0x0000030e00000000

def z180 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0x60e619fe7c070662 0x2c1cc33fcf80e0cc

def z181 : W := mkw 0x0000000000000000 0x0000000000000000 0x8019e00000000001 0xd0033c0000000000

def z182 : W := mkw 0x15b81fd01ef82fae 0x22b703fa03df05f5 0xdff81ff00ff8fffe 0xfbff03fe01ff1fff

def z183 : W := mkw 0x04b000000b56d000 0x00960000016ada00 0xdff800000ffff804 0xfbff000001ffff00

def z184 : W := mkw 0x0000000000000000 0x0000000000000000 0x0018e00000787800 0x80031c00000f0f00

def z185 : W := mkw 0x08082bb6f4292eed 0x61010576de8525dd 0x20001ffff00007fa 0x040003fffe0000ff

def z186 : W := mkw 0x004aa324e0000000 0x000954649c000000 0xe0fffffff0000003 0xfc1ffffffe000000

def z187 : W := mkw 0x27dff76fe1058051 0x84fbfeedfc20b00a 0xeffffffff007807b 0xfdfffffffe00f00f

def z188 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0xaf06180e0f870667 0x35e0c301c1f0e0cc

def z189 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z190 : W := mkw 0x0205000001048000 0x0040a00000209000 0x0807000000078001 0x0100e0000000f000

def z191 : W := mkw 0x26dfe364e0000000 0x04dbfc6c9c000000 0xc7ffe1f070000001 0xf8fffc3e0e000000

def z192 : W := mkw 0x24fae364ea525000 0x049f5c6c9d4a4a00 0x40f8e1f070787800 0x881f1c3e0e0f0f00

def z193 : W := mkw 0x0000008010282aac 0x2000001002050555 0x0000000000787800 0x00000000000f0f00

def z194 : W := mkw 0x27fffffdec600600 0x04ffffffbd8c00c0 0xe7fffffffc600607 0xfcffffffff8c00c0

def z195 : W := mkw 0x0842802650036061 0x41085004ca006c0c 0x2806800e70076061 0x0500d001ce00ec0c

def z196 : W := mkw 0x0008030000000000 0x0001006000000000 0x8018078000000002 0xd00300f000000000

def z197 : W := mkw 0x00082300a0000000 0x0001046014000000 0xa019e781f0000003 0xd4033cf03e000000

def z198 : W := mkw 0x10280b900ef80786 0x0205017201df00f0 0x901807800ff80786 0xd20300f001ff00f0

def z199 : W := mkw 0x1dfa9ff45efa67a6 0x43bf53fe8bdf4cf4 0xd7f89ff07ff86786 0xfaff13fe0fff0cf0

def z200 : W := mkw 0x0205080b05058451 0x8040a10160a0b08a 0xa807180f8c07867f 0x3500e301f180f0cf

def z201 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0x171806000ff80784 0x42e300c001ff00f0

def z202 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0x2806800e7c676665 0x0500d001cf8ceccc

def z203 : W := mkw 0x31083ffde4a80786 0x062107ffbc9500f0 0x20001ffff0000782 0x040003fffe0000f0

def z204 : W := mkw 0x069d6380b33cbaac 0x20d3ac7016679755 0xbf19e781f3f8ffff 0xd7e33cf03e7f1fff

def z205 : W := mkw 0x00282b90bc682eac 0x20050572178d05d5 0xf8f9fff1fc78ffff 0xff1f3ffe3f8f1fff

def z206 : W := mkw 0x1598174002980186 0x02b302e800530030 0x1718060003980180 0x42e300c000730030

def z207 : W := mkw 0x296abffffc636661 0x452d57ffff8c6ccc 0xe8e69ffffc676667 0xbd1cd3ffff8ceccc

def z208 : W := mkw 0x01001c0004800500 0x00200380009000a0 0x070018000f800000 0x20e0030001f00000

def z209 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0x47e01ff00f800782 0x28fc03fe01f000f0

def z210 : W := mkw 0x15b817d00af80386 0x02b702fa015f0070 0x57f807f003f80180 0xcaff00fe007f0030

def z211 : W := mkw 0x03051c0b04010441 0x0060a38160802088 0xaf071e0f8c070667 0x75e0e3c1f180e0cc

def z212 : W := mkw 0x37ffff7deed00502 0x06ffffefbdda00a0 0xe7ffffffff800003 0xfcfffffffff00000

def z213 : W := mkw 0x15b83fd0aef80f8e 0x22b707fa15df01f1 0xd7f97ff18ff89f9e 0xfaff2ffe31ff13f3

def z214 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xfffffffff00087ff 0xfffffffffe0010ff

def z215 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0x5fe600000ffff804 0x2bfcc00001ffff00

def z216 : W := mkw 0x0b679cbf5de7e771 0xc16cf397ebbcfcee 0xffe79fffffe7e7ff 0xfffcf3fffffcfcff

def z217 : W := mkw 0x0820009018626220 0x41040012030c4c44 0x0000000000606000 0x00000000000c0c00

def z218 : W := mkw 0x0042800000024000 0x0008500000004800 0x0806800000076001 0x0100d0000000ec00

def z219 : W := mkw 0x07f7dc0b0fd7d551 0x80fefb8161fafaaa 0xdffff80e0ffff805 0xfbffff01c1ffff00

def z220 : W := mkw 0x2100146d40000000 0x0420028da8000000 0x0000187e00000000 0x0000030fc0000000

def z221 : W := mkw 0x279d7f4ba5858551 0x84f3afe974b0b0aa 0xbf1f7e0f8f8787ff 0x77e3efc1f1f0f0ff

def z222 : W := mkw 0x086288364c434441 0x410c5106c9886888 0xe0e699fe7c070003 0xbc1cd33fcf80e000

def z223 : W := mkw 0x01001c0204810541 0x00200380409020a8 0xbf061e0e0f8707e7 0x77e0c3c1c1f0e0fc

def z224 : W := mkw 0x27d7d46d40000000 0x04fafa8da8000000 0xe7e71e7f80000003 0x7cfce3cff0000000

def z225 : W := mkw 0x06d7c00000000000 0x00daf80000000000 0x47e6000000000000 0x28fcc00000000000

def z226 : W := mkw 0x0ef7c8364f57d441 0x41def906c9eafa88 0xdffff87e0ffff805 0xfbffff0fc1ffff00

def z227 : W := mkw 0x27dff7ede0280284 0x04fbfefdbc050050 0xf7fffffff0780787 0xfefffffffe0f00f0

def z228 : W := mkw 0x2247e02df0002828 0x2448fc05be000505 0x2807e00ff000f879 0x0500fc01fe001f0f

def z229 : W := mkw 0x102008900ef80786 0x0204011201df00f0 0xd0e019f00ff80786 0xba1c033e01ff00f0

def z230 : W := mkw 0x06d7c02440000000 0x00daf80488000000 0xe7fff9fe70000003 0xfcffff3fce000000

def z231 : W := mkw 0x00002000b0002828 0x2000040016000505 0xb819e001f078f87d 0xd7033c003e0f1f0f

def z232 : W := mkw 0x0cf2c8b65e737661 0x419e5916cbce6ecc 0xe8fef9fe7c7f7e67 0xbd1fdf3fcf8fefcc

def z233 : W := mkw 0x182008921efb67e7 0x4304011243df6cfc 0x180000000fff67e4 0x0300000001ffecfc

def z234 : W := mkw 0x00082380b0282aac 0x2001047016050555 0xa818e18070787e67 0x95031c300e0f0fcc

def z235 : W := mkw 0x07f7d4090b56d000 0x00fefa81216ada00 0xfffffe0f8ffff807 0xffffffc1f1ffff00

def z236 : W := mkw 0x06d7c0000316d000 0x00daf8000062da00 0x1f1fe000039ff801 0x43e3fc000073ff00

def z237 : W := mkw 0x2598376de0000000 0x04b306edbc000000 0xe7f81ffff0000002 0xfcff03fffe000000

def z238 : W := mkw 0x08282b92bc6b6eed 0x61050572578d6ddd 0xb819e781fc7fffff 0xd7033cf03f8fffff

def z239 : W := mkw 0x0205080b05858551 0x8040a10160b0b0aa 0x3807000f8f8787fd 0x0700e001f1f0f0ff

def z240 : W := mkw 0x080008b654212661 0x41000116ca8424cc 0x200019fe70000662 0x0400033fce0000cc

def z241 : W := mkw 0x2247e02de106d000 0x0448fc05bc20da00 0x2807e00ff007f801 0x0500fc01fe00ff00

def z242 : W := mkw 0x14b823d0ba782aae 0x2297047a174f0555 0xf8f9e7f1f078ffff 0xdf1f3cfe3e0f1fff

def z243 : W := mkw 0x279d7749a3149000 0x04f3aee934629200 0x1719660183989800 0x42e32cc030731300

def z244 : W := mkw 0x27d7d46d40000000 0x04fafa8da8000000 0xc7fff87e00000001 0xf8ffff0fc0000000

def z245 : W := mkw 0x15b01cd00ef00702 0x02b6039a01de00e0 0xc7e019f00fe00606 0xb8fc033e01fc00c0

def z246 : W := mkw 0x0a6788b65d67e661 0x414cf116cbacfccc 0xffe799fe7fe7e667 0xfffcf33fcffcfccc

def z247 : W := mkw 0x006288020c434441 0x000c510041886888 0xe8e6980e0c676667 0xbd1cd301c18ceccc

def z248 : W := mkw 0x03251c0b0fd7d551 0x8064a38161fafaaa 0xbf071e0f8fffffff 0x77e0e3c1f1ffffff

def z249 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0x27061e0f8f8707fa 0x24e0c3c1f1f0e0ff

def z250 : W := mkw 0x06f7c0801b76f220 0x00def810036ede44 0xffffe1807ffffe67 0xfffffc300fffffcc

def z251 : W := mkw 0x082008120c434441 0x4104010241886888 0x000000000c070000 0x000000000180e000

def z252 : W := mkw 0x002008020fd7d551 0x8004010041fafaaa 0x180000000ffffffc 0x0300000001ffffff

def z253 : W := mkw 0x0b679cbf5de7e771 0xc16cf397ebbcfcee 0xefe699fe7fe76667 0xbdfcd33fcffceccc

def z254 : W := mkw 0x07f7d4090bd6d110 0x80fefa81217ada22 0xdfffe6018ffff99d 0xfbfffcc031ffff33

def z255 : W := mkw 0x27d7dc6f45858551 0x84fafb8de8b0b0aa 0xffe71e7f8f8787ff 0x7ffce3cff1f0f0ff

def z256 : W := mkw 0x06b500000b548000 0x00d6a000016a9000 0xdfff00000fff8005 0xfbffe00001fff000

def z257 : W := mkw 0x002008900c600600 0x00040112018c00c0 0x000000000c600604 0x00000000018c00c0

def z258 : W := mkw 0x0062800008424000 0x000c500001084800 0x40e600000c070000 0x281cc0000180e000

def z259 : W := mkw 0x27fff76deb56d000 0x04fffeedbd6ada00 0xe7ffffffff870003 0xfcfffffffff0e000

def z260 : W := mkw 0x0305140901848110 0x8060a28120309022 0xbf010601838087ff 0x57e020c0307010ff

def z261 : W := mkw 0x0205000900000000 0x0040a00120000000 0x2007000f80000001 0x0400e001f0000000

def z262 : W := mkw 0x15fa9ff44ef80786 0x02bf53fe89df00f0 0xf7fe9ffe7ff80787 0xfeffd3ffcfff00f0

def z263 : W := mkw 0x0000000000000000 0x0000000000000000 0xa001060180000003 0x540020c030000000

def z264 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0x48e081f07c676664 0x891c103e0f8ceccc

def z265 : W := mkw 0x01001c0b04810551 0x80200381609020aa 0xa8061e0f8c0707ff 0x3500c3c1f180e0ff

def z266 : W := mkw 0x01001c0004800500 0x00200380009000a0 0xbf011e018f8087ff 0x77e023c031f010ff

def z267 : W := mkw 0x37fffffdfef82fae 0x26ffffffbfdf05f5 0xfffffffffff8ffff 0xffffffffffff1fff

def z268 : W := mkw 0x1fff9fff5fffe7f7 0xc3fff3ffebfffcfe 0xffff9fffffffe7ff 0xfffff3fffffffcff

def z269 : W := mkw 0x1590144002900102 0x02b2028800520020 0x0700000003800000 0x00e0000000700000

def z270 : W := mkw 0x17bd1fd90ffc8796 0x82f7a3fb21ff90f2 0xd7f91ff18ff8879e 0xfaff23fe31ff10f3

def z271 : W := mkw 0x0000080004800500 0x00000100009000a0 0x100000000f800784 0x0200000001f000f0

def z272 : W := mkw 0x210837edf0282aac 0x242106fdbe050555 0xb819fffff078ffff 0xd7033ffffe0f1fff

def z273 : W := mkw 0x17bd3fdbbffdafff 0xa2f7a7fb77ffb5ff 0xffffffffffffffff 0xffffffffffffffff

def z274 : W := mkw 0x210837edf0282aac 0x242106fdbe050555 0x20001ffff00007fa 0x040003fffe0000ff

def z275 : W := mkw 0x0000080204010441 0x0000010040802088 0x2000180e00000662 0x04000301c00000cc

def z276 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0x47f9e7f1f0000000 0xc8ff3cfe3e000000

def z277 : W := mkw 0x084288b654212661 0x41085116ca8424cc 0xe0e699fe70000663 0xbc1cd33fce0000cc

def z278 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xf8e79ffffc67e7ff 0xff1cf3ffff8cfcff

def z279 : W := mkw 0x01081f8004a80784 0x002103f0009500f0 0x97181f800ff80786 0xf2e303f001ff00f0

def z280 : W := mkw 0x002000000a525000 0x00040000014a4a00 0x0000000000787800 0x00000000000f0f00

def z281 : W := mkw 0x0ef7c8921f77f661 0x41def91243eefecc 0xdfffe0000ffffe65 0xfbfffc0001ffffcc

def z282 : W := mkw 0x00082300a008088c 0x2001046014010111 0x0018600000181800 0x00030c0000030300

def z283 : W := mkw 0x07b51c0b0fd58551 0x80f6a38161fab0aa 0xffff1e0f8fff87ff 0xffffe3c1f1fff0ff

def z284 : W := mkw 0x00082380b0282aac 0x2001047016050555 0x181966018078fffc 0x43032cc0300f1fff

def z285 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000060000000786 0x520000c0000000f0

def z286 : W := mkw 0x11083fd0b4a82fae 0x222107fa169505f5 0x20001ff1f00007fa 0x040003fe3e0000ff

def z287 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000818070000003 0x940010300e000000

def z288 : W := mkw 0x179d5740039c9186 0x02f3aae800739230 0x1719660003989980 0x42e32cc000731330

def z289 : W := mkw 0x17ffdfd00ef80786 0x02fffbfa01df00f0 0xd7fffff00ff80787 0xfafffffe01ff00f0

def z290 : W := mkw 0x13251c9b0ffd87d7 0x8264a39361ffb0fa 0xbf071e0f8fff87ff 0x77e0e3c1f1fff0ff

def z291 : W := mkw 0x086288365c436461 0x410c5106cb886c8c 0x68e6987e7c076061 0x2d1cd30fcf80ec0c

def z292 : W := mkw 0x08082bb6f4292eed 0x61010576de8525dd 0xb819fffff078ffff 0xd7033ffffe0f1fff

def z293 : W := mkw 0x0b6fbfbffdefeffd 0xe16df7f7ffbdfdff 0xffffffffffffffff 0xffffffffffffffff

def z294 : W := mkw 0x0347942d40000000 0x0068f285a8000000 0xe7e79ffff0000003 0xfcfcf3fffe000000

def z295 : W := mkw 0x05da976440000000 0x00bb52ec88000000 0xe7fe9ffe70000003 0xfcffd3ffce000000

def z296 : W := mkw 0x04d2c00000000000 0x009a580000000000 0x40f8e00000000000 0x881f1c0000000000

def z297 : W := mkw 0x24dae364e0000000 0x049b5c6c9c000000 0x40f8e1f070000000 0x881f1c3e0e000000

def z298 : W := mkw 0x030d3709a18c899c 0xa061a6e134319133 0x1719660183989998 0x42e32cc030731333

def z299 : W := mkw 0x0205000b01058051 0x8040a0016020b00a 0x0006000e00070000 0x0000c001c000e000

def z300 : W := mkw 0x27dfff6fe4810551 0x84fbffedfc9020aa 0xe7fffffff00007fb 0xfcfffffffe0000ff

def z301 : W := mkw 0x026780000946c000 0x004cf0000128d800 0xdfe780000fe7e005 0xfbfcf00001fcfc00

def z302 : W := mkw 0x0205000001048000 0x0040a00000209000 0x9f1fe0000ffff805 0xf3e3fc0001ffff00

def z303 : W := mkw 0x006288b44c600600 0x000c5116898c00c0 0xe0e699fe7c600607 0xbc1cd33fcf8c00c0

def z304 : W := mkw 0x0800083644010441 0x41000106c8802088 0x0000187e00000000 0x0000030fc0000000

def z305 : W := mkw 0x086288364c434441 0x410c5106c9886888 0xc8e6987e0c676005 0xb91cd30fc18cec00

def z306 : W := mkw 0x0490400002101000 0x0092080000420200 0x0018600000181800 0x00030c0000030300

def z307 : W := mkw 0x0000008010202220 0x0000001002040444 0x2000018070000662 0x040000300e0000cc

def z308 : W := mkw 0x0205000b01058051 0x8040a0016020b00a 0xb807060f800787ff 0x5700e0c1f000f0ff

def z309 : W := mkw 0x082008921c636661 0x41040112438c6ccc 0xc8e019f00c676666 0xb91c033e018ceccc

def z310 : W := mkw 0x15983740a298098e 0x22b306e814530131 0x1719660183989998 0x42e32cc030731333

def z311 : W := mkw 0x102008901ef82fae 0x2204011203df05f5 0x180000000ff8fffc 0x0300000001ff1fff

def z312 : W := mkw 0x0247c0000106d000 0x0048f8000020da00 0x981fe000007ff805 0xd303fc00000fff00

def z313 : W := mkw 0x27f7d46d4b56d000 0x04fefa8da96ada00 0xdffff87e0ffff805 0xfbffff0fc1ffff00

def z314 : W := mkw 0x15b81fdb0ef907d7 0x82b703fb61df20fa 0xf7f81fff8ff807fe 0xfeff03fff1ff00ff

def z315 : W := mkw 0x06d7c00000000000 0x00daf80000000000 0xdfffe0000078f805 0xfbfffc00000f1f00

def z316 : W := mkw 0x0ff7dcbf5ff7f771 0xc1fefb97ebfefeee 0xffffffffffffffff 0xffffffffffffffff

def z317 : W := mkw 0x00082380b0282aac 0x2001047016050555 0x9819e1807078f805 0xd3033c300e0f1f00

def z318 : W := mkw 0x14b80bd00e780686 0x0297017a01cf00d0 0xc0f819f00c780606 0xb81f033e018f00c0

def z319 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000601800007fa 0x040000c0300000ff

def z320 : W := mkw 0x09629cb65ce36761 0x412c5396cb9c6cec 0xffe69ffe7fe767e7 0xfffcd3ffcffcecfc

def z321 : W := mkw 0x102000900a780286 0x02040012014f0050 0x0000000000780000 0x00000000000f0000

def z322 : W := mkw 0x234ff76de0000000 0x0469feedbc000000 0x2007fffff0000003 0x0400fffffe000000

def z323 : W := mkw 0x27d7dc6f45858551 0x84fafb8de8b0b0aa 0x47e6187e0f870000 0x28fcc30fc1f0e000

def z324 : W := mkw 0x0305140901848110 0x8060a28120309022 0x9f0706018f87819d 0x73e0e0c031f0f033

def z325 : W := mkw 0x086288b65c6b6eed 0x610c5116cb8d6ddd 0xf8e699fe7c7fffff 0xbf1cd33fcf8fffff

def z326 : W := mkw 0x00082300a008088c 0x2001046014010111 0x9819e6018078f99d 0xd3033cc0300f1f33

def z327 : W := mkw 0x27fff7edfb7efaac 0x24fffefdbf6fdf55 0xffffffffffffffff 0xffffffffffffffff

def z328 : W := mkw 0x15b01c500ed00502 0x02b6038a01da00a0 0xd7f818700ff80004 0xfaff030e01ff0000

def z329 : W := mkw 0x086aa3b4f86a6aac 0x610d54769f0d4d55 0x40f8e1f070787800 0x881f1c3e0e0f0f00

def z330 : W := mkw 0x2247c02d40000000 0x0448f805a8000000 0x0006000e00000000 0x0000c001c0000000

def z331 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0x47fef9fe70000000 0xa8ffdf3fce000000

def z332 : W := mkw 0x03051c8b15a5a771 0x8060a39162b4b4ee 0xbf079f8fffe7e7ff 0xf7e0f3f1fffcfcff

def z333 : W := mkw 0x01001c0b05858551 0x8020038160b0b0aa 0x38001e0f8f8787fe 0x070003c1f1f0f0ff

def z334 : W := mkw 0x086288921c636661 0x410c5112438c6ccc 0xc8e680000c676665 0xb91cd000018ceccc

def z335 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xfffffffff078f807 0xfffffffffe0f1f00

def z336 : W := mkw 0x0842802640034041 0x41085004c8006808 0x0006000e00070000 0x0000c001c000e000

def z337 : W := mkw 0x0205080205058441 0x0040a10040a0b088 0xbf07180e0f878667 0x77e0e301c1f0f0cc

def z338 : W := mkw 0x05b817400a500000 0x00b702e8014a0000 0xd7f81ff00ff80006 0xfaff03fe01ff0000

def z339 : W := mkw 0x179d1f4b079d85d7 0x82f3a3e960f3b0ba 0xbf1f1e0f8f9f87ff 0x77e3e3c1f1f3f0ff

def z340 : W := mkw 0x27dfff6fe5858551 0x84fbffedfcb0b0aa 0xe7ffffffff870003 0xfcfffffffff0e000

def z341 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0xbf1ffe0f8fffffff 0xf7e3ffc1f1ffffff

def z342 : W := mkw 0x05983740a0000000 0x00b306e814000000 0xe7f9fff1f0000003 0xfcff3ffe3e000000

def z343 : W := mkw 0x1498034002180086 0x0293006800430010 0x0018000000180000 0x0003000000030000

def z344 : W := mkw 0x14b80bd00ef80786 0x0297017a01df00f0 0x50f801f00ff80784 0x8a1f003e01ff00f0

def z345 : W := mkw 0x0cf2c0b45a727220 0x419e58168b4e4e44 0x40f8e1f070787800 0x881f1c3e0e0f0f00

def z346 : W := mkw 0x030d3f0ba5858551 0x8061a7e174b0b0aa 0xbf1fff8fff8787ff 0xf7e3fff1fff0f0ff

def z347 : W := mkw 0x00082380b0282aac 0x2001047016050555 0x2819e181f078f879 0x85033c303e0f1f0f

def z348 : W := mkw 0x0000008010202220 0x0000001002040444 0xb8018781f060e7ff 0xd70030f03e0c1cff

def z349 : W := mkw 0x00082b82b5adaffd 0xa001057056b5b5ff 0xb819e781ffffffff 0xd7033cf03fffffff

def z350 : W := mkw 0x000000000106d000 0x000000000020da00 0x080000000007f800 0x010000000000ff00

def z351 : W := mkw 0x0100140900000000 0x0020028120000000 0x20001e0f80000002 0x040003c1f0000000

def z352 : W := mkw 0x0ef7c0b45b76f220 0x41def8168b6ede44 0xdfffe1f07ffff805 0xfbfffc3e0fffff00

def z353 : W := mkw 0x0305140900000000 0x0060a28120000000 0xbf071e0f800087ff 0x77e0e3c1f00010ff

def z354 : W := mkw 0x0000080204010441 0x0000010040802088 0x080000000c070664 0x010000000180e0cc

def z355 : W := mkw 0x04b82380ba782aac 0x20970470174f0555 0xfff9e781fff8ffff 0xffff3cf03fff1fff

def z356 : W := mkw 0x37dffffde4a80786 0x06fbffffbc9500f0 0xe7fffffff0000783 0xfcfffffffe0000f0

def z357 : W := mkw 0x37f7dc7d4ed00502 0x06fefb8fa9da00a0 0x47e6187e0f800000 0x28fcc30fc1f00000

def z358 : W := mkw 0x0205000001048000 0x0040a00000209000 0x070600000f870000 0x20e0c00001f0e000

def z359 : W := mkw 0x082008921c6b6eed 0x61040112438d6ddd 0x180000000c7ffffc 0x03000000018fffff

def z360 : W := mkw 0x37ffdffd4ef80786 0x06fffbffa9df00f0 0xd7fe1ffe0ff80786 0xfaffc3ffc1ff00f0

def z361 : W := mkw 0x0000080204810551 0x80000100409020aa 0x00000000000007f8 0x00000000000000ff

def z362 : W := mkw 0x082008921de7e771 0xc104011243bcfcee 0x180000000fe7e7fc 0x0300000001fcfcff

def z363 : W := mkw 0x26dfe36de0000000 0x04dbfc6dbc000000 0x60ffe1fff0000001 0x8c1ffc3ffe000000

def z364 : W := mkw 0x00082380b0282aac 0x2001047016050555 0x1818e1807078fffc 0x83031c300e0f1fff

def z365 : W := mkw 0x082008b65c636661 0x41040116cb8c6ccc 0x280019fe7c676666 0x0500033fcf8ceccc

def z366 : W := mkw 0x06f7c0000a500000 0x00def800014a0000 0xd7ffe0000ff80005 0xfafffc0001ff0000

def z367 : W := mkw 0x0305140b01058051 0x8060a2816020b00a 0xaf071e0f8007807b 0x75e0e3c1f000f00f

def z368 : W := mkw 0x279d7749a0000000 0x04f3aee934000000 0xa71f7e0f80000003 0x74e3efc1f0000000

def z369 : W := mkw 0x07f7dc000fd6d500 0x00fefb8001fadaa0 0xdffffe000fffff87 0xfbffffc001fffff0

def z370 : W := mkw 0x0020000008400000 0x0004000001080000 0xc0e000000c600004 0xb81c0000018c0000

def z371 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0x1f0106018f8787fc 0x43e020c031f0f0ff

def z372 : W := mkw 0x26f7e02deb56d000 0x04defc05bd6ada00 0xffffe00ffffff805 0xfffffc01ffffff00

def z373 : W := mkw 0x086280b658636261 0x410c5016cb0c6c4c 0x68e681fe70676061 0x8d1cd03fce0cec0c

def z374 : W := mkw 0x03051c0b04810551 0x8060a381609020aa 0xa7071e0f800007fb 0x74e0e3c1f00000ff

def z375 : W := mkw 0x17bd1fdb0ffd87d7 0x82f7a3fb61ffb0fa 0xd7fe1ffe0fff0786 0xfaffc3ffc1ffe0f0

def z376 : W := mkw 0x0800000210036061 0x4100000042006c0c 0x0800000000076060 0x010000000000ec0c

def z377 : W := mkw 0x1dfa9ff64efb47c7 0x43bf53fec9df68f8 0xd7fe1ffe0fff0786 0xfaffc3ffc1ffe0f0

def z378 : W := mkw 0x0490000000000000 0x0092000000000000 0xc7f8000000000000 0xf8ff000000000000

def z379 : W := mkw 0x086a8bb65c6b66e5 0x410d5176cb8d6cdc 0xf8fe9ffe7c7f67e7 0xff1fd3ffcf8fecfc

def z380 : W := mkw 0x004280a450202220 0x000850148a040444 0xe8e699fe70606667 0xbd1cd33fce0c0ccc

def z381 : W := mkw 0x01201c900ce00700 0x00240392019c00e0 0xd7e01ff00fe00786 0xfafc03fe01fc00f0

def z382 : W := mkw 0x1000089004a80786 0x02000112009500f0 0x0000000000000780 0x00000000000000f0

def z383 : W := mkw 0x0a47802f5107e071 0xc148f005ea20fc0e 0x2807800ff007e079 0x0500f001fe00fc0f

def z384 : W := mkw 0x14fac3d00a7a5286 0x029f587a014f4a50 0x40f8e1f000787800 0x881f1c3e000f0f00

def z385 : W := mkw 0x0000080205858551 0x8000010040b0b0aa 0xb80106018f8787ff 0x570020c031f0f0ff

def z386 : W := mkw 0x082008921c636661 0x41040112438c6ccc 0xa80081807c676667 0x950010300f8ceccc

def z387 : W := mkw 0x15fadfd00efa5786 0x02bf5bfa01df4af0 0xd7f8fff00ff87f86 0xfaff1ffe01ff0ff0

def z388 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0x40f81ff000780782 0x881f03fe000f00f0

def z389 : W := mkw 0x15fa9fd00efa4786 0x02bf53fa01df48f0 0xdffe9ff00fff6787 0xfbffd3fe01ffecf0

def z390 : W := mkw 0x16f7c8900ffed786 0x02def91201ffdaf0 0xdfffe0000fffff85 0xfbfffc0001fffff0

def z391 : W := mkw 0x0000000000000000 0x0000000000000000 0x1001060180008198 0x420020c030001033

def z392 : W := mkw 0x0062800008424000 0x000c500001084800 0xd8ffe0000c7ff805 0xfb1ffc00018fff00

def z393 : W := mkw 0x059817c000280284 0x00b302f800050050 0xd7f81ff000780786 0xfaff03fe000f00f0

def z394 : W := mkw 0x0062802448424000 0x000c500489084800 0xe8e699fe7c676007 0xbd1cd33fcf8cec00

def z395 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0x47f819f00ff80000 0xa8ff033e01ff0000

def z396 : W := mkw 0x17f7dc500fd6d502 0x02fefb8a01fadaa0 0xdffff8700ffff805 0xfbffff0e01ffff00

def z397 : W := mkw 0x27dfffeff5adaffd 0xa4fbfffdfeb5b5ff 0xffffffffffffffff 0xffffffffffffffff

def z398 : W := mkw 0x086aabb6fc6b6eed 0x610d5576df8d6ddd 0xe8fef9fe7c7f7e67 0xbd1fdf3fcf8fefcc

def z399 : W := mkw 0x0008038000280284 0x0001007000050050 0x0000078000000782 0x000000f0000000f0

def z400 : W := mkw 0x0347dc0b0587d551 0x8068fb8160b0faaa 0xbf07fe0f8f87ffff 0x77e0ffc1f1f0ffff

def z401 : W := mkw 0x0598174000000000 0x00b302e800000000 0x0718060000000000 0x40e300c000000000

def z402 : W := mkw 0x186288b65efb67e7 0x430c5116cbdf6cfc 0xf8e699fe7fff67e7 0xbf1cd33fcfffecfc

def z403 : W := mkw 0x04b000000a500000 0x00960000014a0000 0xdff9e0000ff8f805 0xfbff3c0001ff1f00

def z404 : W := mkw 0x17b51c5b0fd58553 0x82f6a38b61fab0aa 0xffe71e7f8f8787ff 0x7ffce3cff1f0f0ff

def z405 : W := mkw 0x2042e024e0000000 0x04085c049c000000 0x0000e00070000000 0x00001c000e000000

def z406 : W := mkw 0x27dfff6fe4010441 0x04fbffedfc802088 0xeffffffffc070667 0xfdffffffff80e0cc

def z407 : W := mkw 0x086aa3b4f86a6aac 0x610d54769f0d4d55 0xf8f9e7f1f078ffff 0xdf1f3cfe3e0f1fff

def z408 : W := mkw 0x06d7c00001048000 0x00daf80000209000 0xdfffe0000f878005 0xfbfffc0001f0f000

def z409 : W := mkw 0x27f7d46d4b56d000 0x04fefa8da96ada00 0x47e6187e0f870000 0x28fcc30fc1f0e000

def z410 : W := mkw 0x379d7749a2980186 0x06f3aee934530030 0x1719660183980180 0x42e32cc030730030

def z411 : W := mkw 0x15b81fd01ef827a6 0x02b703fa03df04f4 0xfff89ff07ff867e7 0xffff13fe0fff0cfc

def z412 : W := mkw 0x084280a650236261 0x41085014ca046c4c 0xa806818e70676667 0x9500d031ce0ceccc

def z413 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0x48ffe000007ff801 0x891ffc00000fff00

def z414 : W := mkw 0x0b679c3f4dc7c551 0xc16cf387e9b8f8aa 0x47e6187e0f870000 0x28fcc30fc1f0e000

def z415 : W := mkw 0x15b81f500ed00502 0x02b703ea01da00a0 0xc7f81ff00f800002 0xf8ff03fe01f00000

def z416 : W := mkw 0x230d376de0000000 0x0461a6edbc000000 0xa7071ffff0000003 0x74e0e3fffe000000

def z417 : W := mkw 0x002008920c610641 0x00040112418c20c8 0xe8e619fe0c670667 0xbd1cc33fc18ce0cc

def z418 : W := mkw 0x11281fd00ef80786 0x022503fa01df00f0 0x10001ff00ff80786 0x020003fe01ff00f0

def z419 : W := mkw 0x002008901c602620 0x00040112038c04c4 0xe8e099f07c606667 0xbd1c133e0f8c0ccc

def z420 : W := mkw 0x082008921c636661 0x41040112438c6ccc 0xa806180e0c676667 0x3500c301c18ceccc

def z421 : W := mkw 0x15981fd004a80786 0x02b303fa009500f0 0xc7f81ff000000782 0xf8ff03fe000000f0

def z422 : W := mkw 0x15b81f500ed80586 0x02b703ea01db00b0 0x57f81e700f980180 0x6aff03ce01f30030

def z423 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0x37011e0f838087fa 0x46e023c1f07010ff

def z424 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0x67e61ffff0000002 0x2cfcc3fffe000000

def z425 : W := mkw 0x06ffc3800b7ed284 0x00dff870016fda50 0xdfffe7800fffff87 0xfbfffcf001fffff0

def z426 : W := mkw 0x0042800000000000 0x0008500000000000 0xc0e6800000000001 0xb81cd00000000000

def z427 : W := mkw 0x00002080b0282aac 0x2000041016050555 0x3801e001f078fffd 0x07003c003e0f1fff

def z428 : W := mkw 0x06dfe300a0000000 0x00dbfc6014000000 0xe7ffe781f0000003 0xfcfffcf03e000000

def z429 : W := mkw 0x15b83fd0aef80786 0x02b707fa15df00f0 0xf7f9fff1fff80787 0xfeff3ffe3fff00f0

def z430 : W := mkw 0x00082300a0000000 0x0001046014000000 0xb819e781f00087ff 0xd7033cf03e0010ff

def z431 : W := mkw 0x086288b65f77f661 0x410c5116cbeefecc 0xf8e699fe7ffffe67 0xbf1cd33fcfffffcc

def z432 : W := mkw 0x0062808018626220 0x000c5010030c4c44 0xe8e681807c676667 0xbd1cd0300f8ceccc

def z433 : W := mkw 0x06ffe300ab56d000 0x00dffc60156ada00 0xffffe781fffff807 0xfffffcf03fffff00

def z434 : W := mkw 0x2795544900000000 0x04f2aa8920000000 0x0700000000000000 0x00e0000000000000

def z435 : W := mkw 0x0795540903949110 0x80f2aa8120729222 0x1719660183989998 0x42e32cc030731333

def z436 : W := mkw 0x05b01c000ed00500 0x00b6038001da00a0 0xd7f81e000ff80786 0xfaff03c001ff00f0

def z437 : W := mkw 0x00082b82b4292eed 0x20010570568525dd 0xb81fff8ffc7fffff 0xf703fff1ff8fffff

def z438 : W := mkw 0x030d3f8bb5adaffd 0xa061a7f176b5b5ff 0xbf071f8fff8787ff 0x77e0e3f1fff0f0ff

def z439 : W := mkw 0x0695400003149000 0x00d2a80000629200 0x0700000003800000 0x00e0000000700000

def z440 : W := mkw 0x06f7c0801b7efaac 0x20def810036fdf55 0xdfffe0000ffffffd 0xfbfffc0001ffffff

def z441 : W := mkw 0x00082380b0282aac 0x2001047016050555 0xb8010781f00087ff 0x570020f03e0010ff

def z442 : W := mkw 0x0000000200010041 0x0000000040002008 0x2806000e00070061 0x0500c001c000e00c

def z443 : W := mkw 0x06f7c00008424000 0x00def80001084800 0xcfffe0000c676005 0xf9fffc00018cec00

def z444 : W := mkw 0x05981f4004800500 0x00b303e8009000a0 0xd7f81ff00f800786 0xfaff03fe01f000f0

def z445 : W := mkw 0x00082380b0282aac 0x2001047016050555 0x38000781f078fffe 0x070000f03e0f1fff

def z446 : W := mkw 0x06f7e000bb56f828 0x20defc00176adf05 0xffffe001fffff87d 0xfffffc003fffff0f

def z447 : W := mkw 0x0020000008424000 0x0004000001084800 0x080000000c676004 0x01000000018cec00

def z448 : W := mkw 0x00282380bb7efaac 0x20050470176fdf55 0xb819e781ffffffff 0xd7033cf03fffffff

def z449 : W := mkw 0x0042802440000000 0x0008500488000000 0x40e081f070000000 0x881c103e0e000000

def z450 : W := mkw 0x2fffffffff77f661 0x45ffffffffeefecc 0xfffffffffffffe67 0xffffffffffffffcc

def z451 : W := mkw 0x11081fd004a80786 0x022103fa009500f0 0x90181ff000780786 0xd20303fe000f00f0

def z452 : W := mkw 0x11081fd004a80786 0x022103fa009500f0 0x97001ff00f800786 0x72e003fe01f000f0

def z453 : W := mkw 0x2247e02fe1058051 0x8448fc05fc20b00a 0x2807e00ff0078079 0x0500fc01fe00f00f

def z454 : W := mkw 0x230d3f6fe5858551 0x8461a7edfcb0b0aa 0xbf071fffff8787ff 0x77e0e3fffff0f0ff

def z455 : W := mkw 0x37bd7fd9aef80786 0x06f7affb35df00f0 0xd7f97ff18ff80786 0xfaff2ffe31ff00f0

def z456 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0x60e099fe70606662 0x8c1c133fce0c0ccc

def z457 : W := mkw 0x0247c0000106d000 0x0048f8000020da00 0x9f07e0000f87f805 0x73e0fc0001f0ff00

def z458 : W := mkw 0x2247e02de0000000 0x0448fc05bc000000 0xe0e7f9fff0000003 0xbc1cff3ffe000000

def z459 : W := mkw 0x006288900c624600 0x000c5112018c48c0 0xc8e699f00c676607 0xb91cd33e018cecc0

def z460 : W := mkw 0x05b81fd00c600600 0x00b703fa018c00c0 0xc7f81ff00c600606 0xf8ff03fe018c00c0

def z461 : W := mkw 0x1cfa8bf65e7b66e7 0x439f517ecbcf6cdc 0xe8fe99fe7c7f6667 0xbd1fd33fcf8feccc

def z462 : W := mkw 0x0000008010202220 0x0000001002040444 0x0000818070606000 0x800010300e0c0c00

def z463 : W := mkw 0x15b83fd0bef82fae 0x22b707fa17df05f5 0xf7f81ff1fff807fe 0xfeff03fe3fff00ff

def z464 : W := mkw 0x34fae3f4ea780286 0x069f5c7e9d4f0050 0x40f8e1f070780000 0x881f1c3e0e0f0000

def z465 : W := mkw 0x04f2c0000a525000 0x009e5800014a4a00 0xd7f8e0000ff87804 0xfaff1c0001ff0f00

def z466 : W := mkw 0x01001c0b04810551 0x80200381609020aa 0xb7001e0f8f8007fe 0x76e003c1f1f000ff

def z467 : W := mkw 0x0108174000000000 0x002102e800000000 0x00001ff000000002 0x000003fe00000000

def z468 : W := mkw 0x07f7dc0b0fd7d551 0x80fefb8161fafaaa 0xffe71e0f8f8787ff 0x7ffce3c1f1f0f0ff

def z469 : W := mkw 0x00002000b0002828 0x2000040016000505 0x20000001f0000078 0x040000003e00000f

def z470 : W := mkw 0x279d7749a0000000 0x04f3aee934000000 0xa719e781f0000003 0xd4e33cf03e000000

def z471 : W := mkw 0x2a67e8bffc636661 0x454cfd17ff8c6ccc 0xe8e7f9fffc676667 0xbd1cff3fff8ceccc

def z472 : W := mkw 0x0000000000000000 0x0000000000000000 0x18000000000087fc 0x03000000000010ff

def z473 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0x17071e0f8f878198 0x62e0e3c1f1f0f033

def z474 : W := mkw 0x030d3709a0000000 0x0061a6e134000000 0xa71fff8ff0000003 0xf4e3fff1fe000000

def z475 : W := mkw 0x27dff7edf0282aac 0x24fbfefdbe050555 0xe7fffffff0787803 0xfcfffffffe0f0f00

def z476 : W := mkw 0x0000008000200200 0x0000001000040040 0x8000018000600606 0x90000030000c00c0

def z477 : W := mkw 0x3ffffffffefb67e7 0x47ffffffffdf6cfc 0xffffffffffff67e7 0xffffffffffffecfc

def z478 : W := mkw 0x080000b450202220 0x410000168a040444 0x000001f070000000 0x0000003e0e000000

def z479 : W := mkw 0x086280b458626220 0x410c50168b0c4c44 0xc8e681f07c676005 0xb91cd03e0f8cec00

def z480 : W := mkw 0x0490000002100000 0x0092000000420000 0x1718000003980000 0x42e3000000730000

def z481 : W := mkw 0x17f7dc500fd6d502 0x02fefb8a01fadaa0 0x47e618700f870000 0x28fcc30e01f0e000

def z482 : W := mkw 0x2000202de0000000 0x04000405bc000000 0x2000000ff0000000 0x04000001fe000000

def z483 : W := mkw 0x01001c0b04810551 0x80200381609020aa 0xb8011e0f800087ff 0x570023c1f00010ff

def z484 : W := mkw 0x25daf764e0000000 0x04bb5eec9c000000 0xc7f8fff070000002 0xf8ff1ffe0e000000

def z485 : W := mkw 0x0205080205858551 0x8040a10040b0b0aa 0x9f0700000f8787fd 0x73e0e00001f0f0ff

def z486 : W := mkw 0x03051c0904800500 0x0060a381209000a0 0xb7071e0f8f800787 0x76e0e3c1f1f000f0

def z487 : W := mkw 0x27dfff6de4800500 0x04fbffedbc9000a0 0xf7ffffffff800787 0xfefffffffff000f0

def z488 : W := mkw 0x0b679c3f4dc7c551 0xc16cf387e9b8f8aa 0xffe71e7f8f8787ff 0x7ffce3cff1f0f0ff

def z489 : W := mkw 0x17ffd7400bded186 0x02fffae8017bda30 0xdfffe6000ffff985 0xfbfffcc001ffff30

def z490 : W := mkw 0x10282b90bef82fae 0x2205057217df05f5 0xb819e781fff8ffff 0xd7033cf03fff1fff

def z491 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xfff91ff18ff887ff 0xffff23fe31ff10ff

def z492 : W := mkw 0x15b81fd20ffd87d7 0x82b703fa41ffb0fa 0xdff81ff00fff87fe 0xfbff03fe01fff0ff

def z493 : W := mkw 0x002000000a500000 0x00040000014a0000 0x100000000ff80004 0x0200000001ff0000

def z494 : W := mkw 0x0000080205858551 0x8000010040b0b0aa 0x000000000f870000 0x0000000001f0e000

def z495 : W := mkw 0x2fffff7fec434441 0x45ffffeffd886888 0xe7fffffffc070003 0xfcffffffff80e000

def z496 : W := mkw 0x0800089214212661 0x41000112428424cc 0x0000000000000660 0x00000000000000cc

def z497 : W := mkw 0x0000008010282aac 0x2000001002050555 0x9819e0000078fffd 0xd3033c00000f1fff

def z498 : W := mkw 0x22056009a0000000 0x0440ac0134000000 0x0001600180000000 0x00002c0030000000

def z499 : W := mkw 0x0100140900800110 0x8020028120100022 0x0000060180000198 0x000000c030000033

def z500 : W := mkw 0x0205000001048000 0x0040a00000209000 0xbf0706018f8787ff 0x77e0e0c031f0f0ff

def z501 : W := mkw 0x07d7d40900000000 0x00fafa8120000000 0xe7fffe0f80000003 0xfcffffc1f0000000

def z502 : W := mkw 0x0a67c8b65d67f661 0x414cf916cbacfecc 0xe8e7f9fe7c67fe67 0xbd1cff3fcf8cffcc

def z503 : W := mkw 0x0205000000000000 0x0040a00000000000 0x8707000000000001 0x70e0e00000000000

def z504 : W := mkw 0x102008920ffd87d7 0x8204011241ffb0fa 0x180000000fff87fc 0x0300000001fff0ff

def z505 : W := mkw 0x00082300b0002828 0x2001046016000505 0xa819e781f000f87b 0xd5033cf03e001f0f

def z506 : W := mkw 0x24dae364e0000000 0x049b5c6c9c000000 0xe0f9e7f1f0000003 0xdc1f3cfe3e000000

def z507 : W := mkw 0x0000000010002020 0x0000000002000404 0x2800800070006061 0x050010000e000c0c

def z508 : W := mkw 0x07dfd74000000000 0x00fbfae800000000 0xc7fffff000000003 0xf8fffffe00000000

def z509 : W := mkw 0x14b008900ef80786 0x0296011201df00f0 0xd7f800000ff80784 0xfaff000001ff00f0

def z510 : W := mkw 0x0008038010282aac 0x2001007002050555 0x981807800078fffe 0xd30300f0000f1fff

def z511 : W := mkw 0x04fae380ba7a7aac 0x209f5c70174f4f55 0xf8f9e781f078ffff 0xdf1f3cf03e0f1fff

def z512 : W := mkw 0x1fffdff65ffff7e7 0x43fffbfecbfffefc 0xfffffffe7fffffe7 0xffffffffcffffffc

def z513 : W := mkw 0x00082380b0282aac 0x2001047016050555 0xa8008781f06067ff 0x950010f03e0c0cff

def z514 : W := mkw 0x0b479c2f5587e571 0xc168f385eab0fcae 0xbf079e0fff87e7ff 0x77e0f3c1fff0fcff

def z515 : W := mkw 0x0695400003149000 0x00d2a80000629200 0x9f19e00003f8f805 0xd3e33c00007f1f00

def z516 : W := mkw 0x002008100c400400 0x0004010201880080 0x40e018700c000000 0x281c030e01800000

def z517 : W := mkw 0x17bd5fd00ffc9786 0x02f7abfa01ff92f0 0xd7f97ff00ff89f86 0xfaff2ffe01ff13f0

def z518 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0x97061e0e0f870786 0x72e0c3c1c1f0e0f0

def z519 : W := mkw 0x17bd1fd00ffc8786 0x02f7a3fa01ff90f0 0xdfff1ff00fff8787 0xfbffe3fe01fff0f0

def z520 : W := mkw 0x196a9ff65ceb67e7 0x432d53fecb9d6cfc 0xe8e69ffe7c6767e7 0xbd1cd3ffcf8cecfc

def z521 : W := mkw 0x0267c0000946d000 0x004cf8000128da00 0xc8e7e0000c67f805 0xb91cfc00018cff00

def z522 : W := mkw 0x00082380b0282aac 0x2001047016050555 0x2801e781f000fffb 0x05003cf03e001fff

def z523 : W := mkw 0x37dff76de2980186 0x06fbfeedbc530030 0xf7fffffff3980183 0xfefffffffe730030

def z524 : W := mkw 0x0042802440000000 0x0008500488000000 0x2006800e70000001 0x0400d001ce000000

def z525 : W := mkw 0x0000000000000000 0x0000000000000000 0xa800000000000667 0x15000000000000cc

def z526 : W := mkw 0x084288b654236661 0x41085116ca846ccc 0x280699fe70076663 0x0500d33fce00eccc

def z527 : W := mkw 0x279d776de0000000 0x04f3aeedbc000000 0x27197ffff0000002 0x44e32ffffe000000

def z528 : W := mkw 0x159817c002b80386 0x02b302f800570070 0x9718078003f80786 0xd2e300f0007f00f0

def z529 : W := mkw 0x086288b64c634641 0x410c5116c98c68c8 0xc0e619fe0c670606 0xb81cc33fc18ce0c0

def z530 : W := mkw 0x37ffffffeffd87d7 0x86fffffffdffb0fa 0xffffffffffff87ff 0xfffffffffffff0ff

def z531 : W := mkw 0x14b000500a500002 0x0296000a014a0000 0x40e0007000000000 0x081c000e00000000

def z532 : W := mkw 0x25daf76de0000000 0x04bb5eedbc000000 0x60f8fffff0000002 0x8c1f1ffffe000000

def z533 : W := mkw 0x00082300a0000000 0x0001046014000000 0x0018e18070000000 0x80031c300e000000

def z534 : W := mkw 0x17bd1fd90ef80786 0x02f7a3fb21df00f0 0xf7ff1fff8ff80787 0xfeffe3fff1ff00f0

def z535 : W := mkw 0x26ffe364eb56d000 0x04dffc6c9d6ada00 0xdfffe1f07ffff805 0xfbfffc3e0fffff00

def z536 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0x271fe60ff0000001 0x44e3fcc1fe000000

def z537 : W := mkw 0x00082380b0282aac 0x2001047016050555 0x0000018070000000 0x000000300e000000

def z538 : W := mkw 0x224fe3adf0282aac 0x2449fc75be050555 0xb81fe78ff078ffff 0xd703fcf1fe0f1fff

def z539 : W := mkw 0x27fff749ab56d000 0x04fffee9356ada00 0xdfffe6018ffff805 0xfbfffcc031ffff00

def z540 : W := mkw 0x0ef7c8b65f77f661 0x41def916cbeefecc 0xefe699fe7fe76667 0xbdfcd33fcffceccc

def z541 : W := mkw 0x00082300a008088c 0x2001046014010111 0x0000060180000198 0x000000c030000033

def z542 : W := mkw 0x2ffffffffc6b6eed 0x65ffffffff8d6ddd 0xfffffffffc7fffff 0xffffffffff8fffff

def z543 : W := mkw 0x0000000010002828 0x2000000002000505 0x080000000000f878 0x0100000000001f0f

def z544 : W := mkw 0x00082300a0000000 0x0001046014000000 0xb819e781f078f807 0xd7033cf03e0f1f00

def z545 : W := mkw 0x279d7749a008088c 0x24f3aee934010111 0x1719660180189998 0x42e32cc030031333

def z546 : W := mkw 0x03051c8b15adaffd 0xa060a39162b5b5ff 0xbf071e0f8fffffff 0x77e0e3c1f1ffffff

def z547 : W := mkw 0x0000000000000000 0x0000000000000000 0x970000000f800004 0x72e0000001f00000

def z548 : W := mkw 0x15b01cd00ef80786 0x02b6039a01df00f0 0x57e018700ff80784 0x2afc030e01ff00f0

def z549 : W := mkw 0x086aabb6fc6b6eed 0x610d5576df8d6ddd 0xe8e69ffffc6767ff 0xbd1cd3ffff8cecff

def z550 : W := mkw 0x01083f80b4a82fac 0x202107f0169505f5 0xbf19ff81fff8ffff 0xf7e33ff03fff1fff

def z551 : W := mkw 0x086288b45c626620 0x410c51168b8c4cc4 0xc0e099f07c606606 0xb81c133e0f8c0cc0

def z552 : W := mkw 0x0205000001048000 0x0040a00000209000 0x1701000003808000 0x42e0200000701000

def z553 : W := mkw 0x27ffff6fefd7d551 0x84ffffedfdfafaaa 0xffffffffffffffff 0xffffffffffffffff

def z554 : W := mkw 0x06f7c8900f76d600 0x00def91201eedac0 0xdffff9f00ffffe07 0xfbffff3e01ffffc0

def z555 : W := mkw 0x04f2c0000a525000 0x009e5800014a4a00 0x40e0000000000000 0x081c000000000000

def z556 : W := mkw 0x0dfa9ff65c636661 0x41bf53fecb8c6ccc 0xeffe9ffe7c676667 0xfdffd3ffcf8ceccc

def z557 : W := mkw 0x01001c0205858551 0x8020038040b0b0aa 0x9f001e000f8787fe 0x73e003c001f0f0ff

def z558 : W := mkw 0x06f7c8020f57d441 0x00def90041eafa88 0xfffff80e0ffffe67 0xffffff01c1ffffcc

def z559 : W := mkw 0x0305140b01858151 0x8060a2816030b02a 0x3f07060f838781f9 0x47e0e0c1f070f03f

def z560 : W := mkw 0x0b679cbf5c636661 0x416cf397eb8c6ccc 0xefe79ffffc676667 0xfdfcf3ffff8ceccc

def z561 : W := mkw 0x27dff76de3149000 0x04fbfeedbc629200 0xf7fffffff3989803 0xfefffffffe731300

def z562 : W := mkw 0x059837c0b0282aac 0x20b306f816050555 0xfff9fff1f078ffff 0xffff3ffe3e0f1fff

def z563 : W := mkw 0x030d3f0ba58d8ddd 0xa061a7e174b1b1bb 0xbf1f7e0f8f9f9fff 0x77e3efc1f1f3f3ff

def z564 : W := mkw 0x0247c00b0107d051 0x8048f8016020fa0a 0x2807e00f8007f879 0x0500fc01f000ff0f

def z565 : W := mkw 0x002000000b56d000 0x00040000016ada00 0x000000000f870000 0x0000000001f0e000

def z566 : W := mkw 0x1db81ff65ef927e7 0x43b703fecbdf24fc 0xf7f81ffe7ff807e6 0xfeff03ffcfff00fc

def z567 : W := mkw 0x27dfd76d40000000 0x04fbfaeda8000000 0xc7fe1ffe00000002 0xf8ffc3ffc0000000

def z568 : W := mkw 0x06f7c0000a525000 0x00def800014a4a00 0xc7ffe00000787801 0xf8fffc00000f0f00

def z569 : W := mkw 0x27fff76dea500000 0x04fffeedbd4a0000 0xf7fffffffff80007 0xfeffffffffff0000

def z570 : W := mkw 0x084aa3a6f02b6aed 0x61095474de056d5d 0xb81fe78ff07fffff 0xd703fcf1fe0fffff

def z571 : W := mkw 0x069d6300a31c988c 0x20d3ac6014639311 0x1719660183989998 0x42e32cc030731333

def z572 : W := mkw 0x00280b900c680684 0x00050172018d00d0 0xd0f81ff00c780786 0xfa1f03fe018f00f0

def z573 : W := mkw 0x0695400003149000 0x00d2a80000629200 0x9f1f60000f9f9805 0x73e3ec0001f3f300

def z574 : W := mkw 0x022500000b56d000 0x0044a000016ada00 0x9f0700000ffff805 0x73e0e00001ffff00

def z575 : W := mkw 0x0008038000280284 0x0001007000050050 0xb8190781807887ff 0xd70320f0300f10ff

def z576 : W := mkw 0x0000002440000000 0x0000000488000000 0x200019fe70000002 0x0400033fce000000

def z577 : W := mkw 0x0effebb6ff7ffeed 0x61dffd76dfefffdd 0xffffffffffffffff 0xffffffffffffffff

def z578 : W := mkw 0x00002000b0002828 0x2000040016000505 0xb801e601f000ffff 0x57003cc03e001fff

def z579 : W := mkw 0x002000801b7efaac 0x20040010036fdf55 0x180000000ffffffc 0x0300000001ffffff

def z580 : W := mkw 0x27dff76df0002828 0x24fbfeedbe000505 0xeffffffff000f87b 0xfdfffffffe001f0f

def z581 : W := mkw 0x09001cbf54a12771 0xc1200397ea9424ee 0x20001ffff00007fa 0x040003fffe0000ff

def z582 : W := mkw 0x0100140000000000 0x0020028000000000 0x87001e0000000002 0x70e003c000000000

def z583 : W := mkw 0x03051c0005848500 0x0060a38000b090a0 0x9f071e000f878787 0x73e0e3c001f0f0f0

def z584 : W := mkw 0x0000000000000000 0x0000000000000000 0x9801000000008005 0x5300200000001000

def z585 : W := mkw 0x0b051cbf55a5a771 0xc160a397eab4b4ee 0xbf071fffff8787ff 0x77e0e3fffff0f0ff

def z586 : W := mkw 0x00082380b0282aac 0x2001047016050555 0xb0180781f07807fe 0xd60300f03e0f00ff

def z587 : W := mkw 0x2a47e02ff0036061 0x4548fc05fe006c0c 0x2807e00ff0076061 0x0500fc01fe00ec0c

def z588 : W := mkw 0x0000000000000000 0x0000000000000000 0x180000000078f804 0x03000000000f1f00

def z589 : W := mkw 0x0305140901848110 0x8060a28120309022 0x0700000003800000 0x00e0000000700000

def z590 : W := mkw 0x080008b654212661 0x41000116ca8424cc 0xa80099fe70606667 0x9500133fce0c0ccc

def z591 : W := mkw 0x06b540000b549000 0x00d6a800016a9200 0xd7f960000ff89804 0xfaff2c0001ff1300

def z592 : W := mkw 0x24986340a0000000 0x04930c6814000000 0x0018600000000000 0x00030c0000000000

def z593 : W := mkw 0x04f2c0000a525000 0x009e5800014a4a00 0xc8fee0000c7f7805 0xb91fdc00018fef00

def z594 : W := mkw 0x00002080b0202a28 0x2000041016040545 0xa801e181f060fe7f 0x95003c303e0c1fcf

def z595 : W := mkw 0x0205000901048010 0x8040a00120209002 0x0001000180008018 0x0000200030001003

def z596 : W := mkw 0x00082380b0282aac 0x2001047016050555 0x30196781f0189ffa 0x46032cf03e0313ff

def z597 : W := mkw 0x2cfae3f4f8626220 0x459f5c7e9f0c4c44 0x40f8e1f070606000 0x881f1c3e0e0c0c00

def z598 : W := mkw 0x0000080204010441 0x0000010040802088 0xb8071e0f8c0787ff 0x7700e3c1f180f0ff

def z599 : W := mkw 0x0000000001048000 0x0000000000209000 0x180000000f878004 0x0300000001f0f000

def z600 : W := mkw 0x15b81fd00ffed786 0x02b703fa01ffdaf0 0xdff81ff00fffff86 0xfbff03fe01fffff0

def z601 : W := mkw 0x0305140900000000 0x0060a28120000000 0x0701060180000000 0x40e020c030000000

def z602 : W := mkw 0x0000000001848110 0x8000000000309022 0x1000000003808198 0x0200000000701033

def z603 : W := mkw 0x37fff7fdea780286 0x06fffeffbd4f0050 0xe7fffffff0780003 0xfcfffffffe0f0000

def z604 : W := mkw 0x2cfaebf6fc636661 0x459f5d7edf8c6ccc 0xe8fef9fe7c676667 0xbd1fdf3fcf8ceccc

def z605 : W := mkw 0x37fffffdeffed786 0x06ffffffbdffdaf0 0xffffffffffffff87 0xfffffffffffffff0

def z606 : W := mkw 0x0000089004200600 0x00000112008400c0 0x000019f000000602 0x0000033e000000c0

def z607 : W := mkw 0x102008900ffed786 0x0204011201ffdaf0 0x180000000fffff84 0x0300000001fffff0

def z608 : W := mkw 0x14b803d00a780286 0x0297007a014f0050 0xd0f807f000780786 0xda1f00fe000f00f0

def z609 : W := mkw 0x17ffdfdb0fffd7d7 0x82fffbfb61fffafa 0xffffffff8fffffff 0xfffffffff1ffffff

def z610 : W := mkw 0x0842802450026020 0x410850048a004c04 0x0000800070006000 0x000010000e000c00

def z611 : W := mkw 0x0000008010282aac 0x2000001002050555 0xb80081807078ffff 0x970010300e0f1fff

def z612 : W := mkw 0x086288b65de7e771 0xc10c5116cbbcfcee 0xf8e699fe7fe7e7ff 0xbf1cd33fcffcfcff

def z613 : W := mkw 0x00082380b0202220 0x0001047016040444 0xa819e781f0606667 0xd5033cf03e0c0ccc

def z614 : W := mkw 0x06d7c0000106d000 0x00daf8000020da00 0xcfffe0000007f801 0xf9fffc000000ff00

def z615 : W := mkw 0x07955c0b07959551 0x80f2ab8160f2b2aa 0xbf1f7e0f8f9f9fff 0x77e3efc1f1f3f3ff

def z616 : W := mkw 0x0000000000000000 0x0000000000000000 0x2801000180008079 0x050020003000100f

def z617 : W := mkw 0x0100140000800100 0x0020028000100020 0x1700060003800180 0x42e000c000700030

def z618 : W := mkw 0x11081fdb04a907d7 0x822103fb609520fa 0x20001fff800007fa 0x040003fff00000ff

def z619 : W := mkw 0x079d174900000000 0x00f3a2e920000000 0xe7ff1fff80000003 0xfcffe3fff0000000

def z620 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0x9f07180e0f878005 0x73e0e301c1f0f000

def z621 : W := mkw 0x0042c00000025000 0x0008580000004a00 0x0000e00000007800 0x00001c0000000f00

def z622 : W := mkw 0x2ff7dc7f4c434441 0x45fefb8fe9886888 0x47e6187e0c070000 0x28fcc30fc180e000

def z623 : W := mkw 0x130d1fdb05ad87d7 0x8261a3fb60b5b0fa 0xbf071fff8f8787ff 0x77e0e3fff1f0f0ff

def z624 : W := mkw 0x06f7c00b0b57d051 0x80def801616afa0a 0xffffe00f8ffff87d 0xfffffc01f1ffff0f

def z625 : W := mkw 0x2347f42de0000000 0x0468fe85bc000000 0xa707fe0ff0000003 0x74e0ffc1fe000000

def z626 : W := mkw 0x00080380102822a4 0x0001007002050454 0xb8188780707867e7 0xd70310f00e0f0cfc

def z627 : W := mkw 0x04b000000a500000 0x00960000014a0000 0x40f8000000780000 0x881f0000000f0000

def z628 : W := mkw 0x0cf288b65e736661 0x419e5116cbce6ccc 0xfffe99fe7fff6667 0xffffd33fcfffeccc

def z629 : W := mkw 0x24d2c06440000000 0x049a580c88000000 0x40e0007000000000 0x081c000e00000000

def z630 : W := mkw 0x0247e000b106f828 0x2048fc001620df05 0x2807e001f007f879 0x0500fc003e00ff0f

def z631 : W := mkw 0x11281fd00ce80786 0x022503fa019d00f0 0xc0e01ff00c600786 0xb81c03fe018c00f0

def z632 : W := mkw 0x04fae380ba7a7aac 0x209f5c70174f4f55 0x40f8e18070787800 0x881f1c300e0f0f00

def z633 : W := mkw 0x00002000a0000808 0x2000040014000101 0x0001600180009818 0x00002c0030001303

def z634 : W := mkw 0x27fff76dea525000 0x04fffeedbd4a4a00 0xe7fffffff0787803 0xfcfffffffe0f0f00

def z635 : W := mkw 0x0000080004000400 0x0000010000800080 0x800018000c000606 0x30000300018000c0

def z636 : W := mkw 0x0498034000000000 0x0093006800000000 0x40f801f000000000 0x881f003e00000000

def z637 : W := mkw 0x04f2c0000a525000 0x009e5800014a4a00 0xd8f9e0000078f805 0xdb1f3c00000f1f00

def z638 : W := mkw 0x04b803800a780284 0x00970070014f0050 0xd7f807800ff80786 0xfaff00f001ff00f0

def z639 : W := mkw 0x0305140901048000 0x0060a28120209000 0xbf071e0f8f878007 0x77e0e3c1f1f0f000

def z640 : W := mkw 0x079d1f4b05858551 0x80f3a3e960b0b0aa 0xffff1fff8f8787ff 0xffffe3fff1f0f0ff

def z641 : W := mkw 0x0062800008424000 0x000c500001084800 0x40e0800000606000 0x881c1000000c0c00

def z642 : W := mkw 0x0800002650012061 0x41000004ca00240c 0x2000000e70000060 0x04000001ce00000c

def z643 : W := mkw 0x0862802658436061 0x410c5004cb086c0c 0xe8e6800e7c676065 0xbd1cd001cf8cec0c

def z644 : W := mkw 0x1cfa83f45a7a62a6 0x439f507e8b4f4c54 0x40f881f070786000 0x881f103e0e0f0c00

def z645 : W := mkw 0x279d77c9b0282aac 0x24f3aef936050555 0xbf19e781f078ffff 0xd7e33cf03e0f1fff

def z646 : W := mkw 0x000000000008088c 0x2000000000010111 0x1000000000189998 0x0200000000031333

def z647 : W := mkw 0x0ef7c0265b57f061 0x41def804cb6afe0c 0xffffe00e7ffff865 0xfffffc01cfffff0c

def z648 : W := mkw 0x00082300a0000000 0x0001046014000000 0x0019660180000000 0x40032cc030000000

def z649 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0x1f06180e0f8787fc 0x23e0c301c1f0f0ff

def z650 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0xa7071e0f8f870003 0x74e0e3c1f1f0e000

def z651 : W := mkw 0x100803d000280286 0x0201007a00050050 0x000001f000000000 0x0000003e00000000

def z652 : W := mkw 0x1108174000880186 0x022102e800110030 0x0000060000000180 0x000000c000000030

def z653 : W := mkw 0x27dff7edf0202220 0x04fbfefdbe040444 0xeffffffff0606667 0xfdfffffffe0c0ccc

def z654 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0xc7ffe0000f870001 0xf8fffc0001f0e000

def z655 : W := mkw 0x0862803448424000 0x410c500689084800 0x40e0007000000000 0x081c000e00000000

def z656 : W := mkw 0x080008b654212661 0x41000116ca8424cc 0xa80619fe7c070667 0x3500c33fcf80e0cc

def z657 : W := mkw 0x15981fd006b80786 0x02b303fa00d700f0 0x17181ff003980782 0x42e303fe007300f0

def z658 : W := mkw 0x2347fc2fe5858551 0x8468ff85fcb0b0aa 0xbf07fe0fff8787ff 0x77e0ffc1fff0f0ff

def z659 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800800000606005 0x91001000000c0c00

def z660 : W := mkw 0x26d7e02de0000000 0x04dafc05bc000000 0xe7ffe00ff0000001 0xfcfffc01fe000000

def z661 : W := mkw 0x0008030000080084 0x0001006000010010 0x1018060000180180 0x420300c000030030

def z662 : W := mkw 0x01083f8bb4a92ffd 0xa02107f1769525ff 0xb819ff8ff078ffff 0xd7033ff1fe0f1fff

def z663 : W := mkw 0x2ffffffffde7e771 0xc5ffffffffbcfcee 0xffffffffffe7e7ff 0xfffffffffffcfcff

def z664 : W := mkw 0x0000088214212661 0x00000110428424cc 0xa806998e7c676667 0xb500d331cf8ceccc

def z665 : W := mkw 0x00082380b0282aac 0x2001047016050555 0xa019e781f00007fb 0xd4033cf03e0000ff

def z666 : W := mkw 0x0305140900000000 0x0060a28120000000 0x0706180e00000000 0x20e0c301c0000000

def z667 : W := mkw 0x0000000000000000 0x0000000000000000 0x0801e0000000f801 0x01003c0000001f00

def z668 : W := mkw 0x00082380b0282aac 0x2001047016050555 0x2018e781f0787ffa 0x84031cf03e0f0fff

def z669 : W := mkw 0x16ffc3d00b7ed286 0x02dff87a016fda50 0xdfffe1f00ffff805 0xfbfffc3e01ffff00

def z670 : W := mkw 0x29083ffff4212661 0x452107fffe8424cc 0x20001ffff0000662 0x040003fffe0000cc

def z671 : W := mkw 0x0000000201058051 0x800000004020b00a 0x0800000000078078 0x010000000000f00f

def z672 : W := mkw 0x086288364c434441 0x410c5106c9886888 0xe8e6187e0c070667 0x3d1cc30fc180e0cc

def z673 : W := mkw 0x24dae3e4f0282aac 0x249b5c7c9e050555 0xf8f9e7f1f078ffff 0xdf1f3cfe3e0f1fff

def z674 : W := mkw 0x0008038000280284 0x0001007000050050 0x0018018000780000 0x80030030000f0000

def z675 : W := mkw 0x002000000b56d000 0x00040000016ada00 0x9819e0000ffff805 0xd3033c0001ffff00

def z676 : W := mkw 0x0000000b00010051 0x800000016000200a 0x2000000f80000078 0x04000001f000000f

def z677 : W := mkw 0x0000000000000000 0x0000000000000000 0xa006180e00000003 0x3400c301c0000000

def z678 : W := mkw 0x00002000b0002828 0x2000040016000505 0x0000e00070007800 0x00001c000e000f00

def z679 : W := mkw 0x07d7dc0b05858551 0x80fafb8160b0b0aa 0xfffffe0f8f8787ff 0xffffffc1f1f0f0ff

def z680 : W := mkw 0x006280000b56d000 0x000c5000016ada00 0xd8e680000ffff805 0xbb1cd00001ffff00

def z681 : W := mkw 0x2ff7dcff5c636661 0x45fefb9feb8c6ccc 0xefe699fe7c676667 0xbdfcd33fcf8ceccc

def z682 : W := mkw 0x020d2380b12caaac 0x2041a47016259555 0xbf1fe781ffffffff 0xf7e3fcf03fffffff

def z683 : W := mkw 0x179d1749039c8196 0x82f3a2e920739032 0x1719060183988198 0x42e320c030731033

def z684 : W := mkw 0x0ef7c8364f57d441 0x41def906c9eafa88 0x47e6187e0f870000 0x28fcc30fc1f0e000

def z685 : W := mkw 0x0a6788bf5d67e671 0xc14cf117ebacfcce 0xe8e799fffc67e67f 0xbd1cf33fff8cfccf

def z686 : W := mkw 0x35b83ffdeef80786 0x06b707ffbddf00f0 0xf7f81ffffff80786 0xfeff03ffffff00f0

def z687 : W := mkw 0x0842a026f0036869 0x61085404de006d0d 0x2807e00ff007f879 0x0500fc01fe00ff0f

def z688 : W := mkw 0x17b51c5b0fd58553 0x82f6a38b61fab0aa 0x47e6187e0f870000 0x28fcc30fc1f0e000

def z689 : W := mkw 0x030d3789b0282aac 0x2061a6f136050555 0xbf1fff8ff078ffff 0xf7e3fff1fe0f1fff

def z690 : W := mkw 0x024fe380b12efaac 0x2049fc701625df55 0xb81fe781f07fffff 0xd703fcf03e0fffff

def z691 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0x28071e0f800787fb 0x0500e3c1f000f0ff

def z692 : W := mkw 0x03251c9b0de58751 0x8064a39361bcb0ea 0xffe71fff8fe787ff 0xfffce3fff1fcf0ff

def z693 : W := mkw 0x27dff7edf0282aac 0x24fbfefdbe050555 0xe7fffffff00007fb 0xfcfffffffe0000ff

def z694 : W := mkw 0x0205000b01058051 0x8040a0016020b00a 0xbf07000f8f87807d 0x77e0e001f1f0f00f

def z695 : W := mkw 0x1df29c764ed34543 0x43be538ec9da68a8 0x47e6187e0f870000 0x28fcc30fc1f0e000

def z696 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0xd7fe00000fff0004 0xfaffc00001ffe000

def z697 : W := mkw 0x0ef7c8b65c636661 0x41def916cb8c6ccc 0xeffff9fe7c676667 0xfdffff3fcf8ceccc

def z698 : W := mkw 0x0000080204010441 0x0000010040802088 0x0006180e0c070000 0x2000c301c180e000

def z699 : W := mkw 0x03679c0b0dc7c551 0x806cf38161b8f8aa 0xffe79e0f8fe7e7ff 0xfffcf3c1f1fcfcff

def z700 : W := mkw 0x0000008010282aac 0x2000001002050555 0x00000000000007f8 0x00000000000000ff

def z701 : W := mkw 0x0000008010202220 0x0000001002040444 0xb819e1807078fe67 0xd7033c300e0f1fcc

def z702 : W := mkw 0x11083fd0b4a82fae 0x222107fa169505f5 0xb819fff1f078ffff 0xd7033ffe3e0f1fff

def z703 : W := mkw 0x07ffd7400b56d000 0x00fffae8016ada00 0xdffffff00ffff807 0xfbfffffe01ffff00

def z704 : W := mkw 0x00082380a0280284 0x0001047014050050 0xb019e781f0780787 0xd6033cf03e0f00f0

def z705 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0xcfe680000fe76005 0xb9fcd00001fcec00

def z706 : W := mkw 0x0000000003149000 0x0000000000629200 0x1000000003989800 0x0200000000731300

def z707 : W := mkw 0x0862c8b65c637661 0x410c5916cb8c6ecc 0xe8e6f9fe7c677e67 0xbd1cdf3fcf8cefcc

def z708 : W := mkw 0x159837c0b2b82bae 0x22b306f816570575 0xfff9fff1f3f8ffff 0xffff3ffe3e7f1fff

def z709 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xd7f9fff00ff80787 0xfaff3ffe01ff00f0

def z710 : W := mkw 0x0a47802f4107c051 0xc148f005e820f80a 0x2807000f80078079 0x0500e001f000f00f

def z711 : W := mkw 0x05901c4004800500 0x00b20388009000a0 0x47e018700f800000 0x28fc030e01f00000

def z712 : W := mkw 0x082008921d67e671 0xc104011243acfcce 0x080000000c67e67c 0x01000000018cfccf

def z713 : W := mkw 0x086288365c436461 0x410c5106cb886c8c 0xe8e699fe7c076063 0xbd1cd33fcf80ec0c

def z714 : W := mkw 0x15b81fd00efa5786 0x02b703fa01df4af0 0xd7f81ff00ff87f86 0xfaff03fe01ff0ff0

def z715 : W := mkw 0x25daf76de0000000 0x04bb5eedbc000000 0xe7f8fffff0000002 0xfcff1ffffe000000

def z716 : W := mkw 0x00082380b0282aac 0x2001047016050555 0xb81fff8ff078ffff 0xf703fff1fe0f1fff

def z717 : W := mkw 0x16bd03db0b7d82d7 0x82d7a07b616fb05a 0x68ff01ff807f8079 0x8d1fe03ff00ff00f

def z718 : W := mkw 0x15b83fdbbef92fff 0xa2b707fb77df25ff 0xf7f81ffffff807fe 0xfeff03ffffff00ff

def z719 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0xdffff9f00ffff807 0xfbffff3e01ffff00

def z720 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0x5ffee0000ffff804 0xabffdc0001ffff00

def z721 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0x48e699fe7c676664 0xa91cd33fcf8ceccc

def z722 : W := mkw 0x030d3f8bb5adaffd 0xa061a7f176b5b5ff 0x071ef98e7fff7800 0xa0e3df31cfffef00

def z723 : W := mkw 0x0a47c0a65127f261 0x4148f814ca24fe4c 0xb81fe18e707ffe67 0xd703fc31ce0fffcc

def z724 : W := mkw 0x15b01c520ed10543 0x02b6038a41da20a8 0x47e6187e0f870000 0x28fcc30fc1f0e000

def z725 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0x2f071e0f8f8787fb 0x25e0e3c1f1f0f0ff

def z726 : W := mkw 0x082008921c612661 0x41040112438c24cc 0x000000000c600664 0x00000000018c00cc

def z727 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0x1f1fe0000ffff805 0x43e3fc0001ffff00

def z728 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xe8e7f9fe7c67fe67 0xbd1cff3fcf8cffcc

def z729 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xf7f89ff07ff80787 0xfeff13fe0fff00f0

def z730 : W := mkw 0x224fe32de0000000 0x0449fc65bc000000 0xe0fffffff0000003 0xfc1ffffffe000000

def z731 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xc7f81ff00ff80002 0xf8ff03fe01ff0000

def z732 : W := mkw 0x15b01cd01ef02722 0x02b6039a03de04e4 0xefe099f07fe06667 0xbdfc133e0ffc0ccc

def z733 : W := mkw 0x2042e024e0000000 0x04085c049c000000 0xe0e6f9fe70000003 0xbc1cdf3fce000000

def z734 : W := mkw 0x04f2c0000a525000 0x009e5800014a4a00 0xdffee0000fff7805 0xfbffdc0001ffef00

def z735 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0xffffe0000ffffe67 0xfffffc0001ffffcc

def z736 : W := mkw 0x15b81fd90ef80796 0x82b703fb21df00f2 0xd7f81ff18ff8079e 0xfaff03fe31ff00f3

def z737 : W := mkw 0x1dda9766529b61e7 0x43bb52ecca536c3c 0x3f1e860e739f61e1 0x47e3d0c1ce73ec3c

def z738 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xeffffffff0606007 0xfdfffffffe0c0c00

def z739 : W := mkw 0x224fe32fe1058051 0x8449fc65fc20b00a 0xb81fe78ff00787ff 0xd703fcf1fe00f0ff

def z740 : W := mkw 0x1db83fd2befb6fef 0x63b707fa57df6dfd 0xfff9fff1ffffffff 0xffff3ffe3fffffff

def z741 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xe0e699fe7c676003 0xbc1cd33fcf8cec00

def z742 : W := mkw 0x15b01c500ed00502 0x02b6038a01da00a0 0xffe11e718f8087ff 0x7ffc23ce31f010ff

def z743 : W := mkw 0x086aab36ec4b4ccd 0x610d5566dd896999 0x50ff7e7f8c1f9998 0x6a1fefcff183f333

def z744 : W := mkw 0x0247c0000106d000 0x0048f8000020da00 0x9f1fe0000ffff805 0xf3e3fc0001ffff00

def z745 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xf8e69ffe7c6767e7 0xff1cd3ffcf8cecfc

def z746 : W := mkw 0x05b81fd00ce00700 0x00b703fa019c00e0 0xd7f81ff00fe00786 0xfaff03fe01fc00f0

def z747 : W := mkw 0x0598174000800100 0x00b302e800100020 0xd7f81ff003800182 0xfaff03fe00700030

def z748 : W := mkw 0x04b803400a500000 0x00970068014a0000 0xd7f801f00ff80004 0xfaff003e01ff0000

def z749 : W := mkw 0x15b81fd00efa4786 0x02b703fa01df48f0 0xdff81ff00fff6786 0xfbff03fe01ffecf0

def z750 : W := mkw 0x15b83f50aed80d8e 0x22b707ea15db01b1 0x57f97e718f989998 0x6aff2fce31f31333

def z751 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xf8e699fe7c67e7ff 0xbf1cd33fcf8cfcff

def z752 : W := mkw 0x082008921defeffd 0xe104011243bdfdff 0x180000000ffffffc 0x0300000001ffffff

def z753 : W := mkw 0x1db81fd21efb67e7 0x43b703fa43df6cfc 0x1f1806000fff67e4 0x43e300c001ffecfc

def z754 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0xbf079e0f8fe7e7ff 0xf7e0f3c1f1fcfcff

def z755 : W := mkw 0x15b01c5b0ed10553 0x82b6038b61da20aa 0x47e0187e0f800000 0x28fc030fc1f00000

def z756 : W := mkw 0x27d7d4ed50282aac 0x24fafa9daa050555 0x5fe6187e0078fffc 0x2bfcc30fc00f1fff

def z757 : W := mkw 0x13051c5b05858553 0x8260a38b60b0b0aa 0xbf071e7f8f8787ff 0x77e0e3cff1f0f0ff

def z758 : W := mkw 0x05f2dc0b0ed35551 0x80be5b8161da6aaa 0x60f8fe0f80787ffa 0x8c1f1fc1f00f0fff

def z759 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xe8e79ffffc676667 0xfd1cf3ffff8ceccc

def z760 : W := mkw 0x1598174002980186 0x02b302e800530030 0x57f81e7003980180 0x6aff03ce00730030

def z761 : W := mkw 0x15b81f500ed80586 0x02b703ea01db00b0 0xd7f81e700ff80184 0xfaff03ce01ff0030

def z762 : W := mkw 0x1db81fd21efb6fef 0x63b703fa43df6dfd 0xdff81ff00ffffffe 0xfbff03fe01ffffff

def z763 : W := mkw 0x24daeb66e5858551 0x849b5d6cdcb0b0aa 0x58f8e1f07f8787fc 0x8b1f1c3e0ff0f0ff

def z764 : W := mkw 0x1db81fd21ef927e7 0x43b703fa43df24fc 0xd7f81ff00ff807e6 0xfaff03fe01ff00fc

def z765 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xe8e799fffc67e67f 0xbd1cf33fff8cfccf

def z766 : W := mkw 0x27dff76de008088c 0x24fbfeedbc010111 0xe7fffffff000019b 0xfcfffffffe000033

def z767 : W := mkw 0x05b817400a500000 0x00b702e8014a0000 0xc7f81ff00f800002 0xf8ff03fe01f00000

def z768 : W := mkw 0x01001c0b04810551 0x80200381609020aa 0xbf061e0f8f8707ff 0x77e0c3c1f1f0e0ff

def z769 : W := mkw 0x082008921c636661 0x41040112438c6ccc 0x000000000c070660 0x000000000180e0cc

def z770 : W := mkw 0x082008921c636661 0x41040112438c6ccc 0x0000000000606660 0x00000000000c0ccc

def z771 : W := mkw 0x15b83fd0bef82fae 0x22b707fa17df05f5 0xdff9fff07ff8ff87 0xfbff3ffe0fff1ff0

def z772 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0xbf1f1e0f8fff87ff 0xf7e3e3c1f1fff0ff

def z773 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0x67e7fffff0000003 0x2cfcfffffe000000

def z774 : W := mkw 0x0305140901048000 0x0060a28120209000 0xbf071e0f8f8787ff 0x77e0e3c1f1f0f0ff

def z775 : W := mkw 0x15b01c5b0ed10553 0x82b6038b61da20aa 0x67e01e7f8f8007fa 0x2cfc03cff1f000ff

def z776 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xf7fe1ffe0ff80787 0xfeffc3ffc1ff00f0

def z777 : W := mkw 0x15b01c500ed00502 0x02b6038a01da00a0 0xdff9f8700ff8f805 0xfbff3f0e01ff1f00

def z778 : W := mkw 0x37dff76de2180086 0x06fbfeedbc430010 0xe7fffffff0180003 0xfcfffffffe030000

def z779 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0x5ff9e0000ffff804 0xcbff3c0001ffff00

def z780 : W := mkw 0x3267e8bdeef80786 0x064cfd17bddf00f0 0x3007e00ffff80785 0x0600fc01ffff00f0

def z781 : W := mkw 0x25daf76de0000000 0x04bb5eedbc000000 0x60e01ffff0000002 0x0c1c03fffe000000

def z782 : W := mkw 0x01201c901ce02720 0x00240392039c04e4 0xffe19ff1ffe0e7ff 0xfffc33fe3ffc1cff

def z783 : W := mkw 0x1cfaa3f4fa7a6aae 0x639f547e9f4f4d55 0x40f8e1f070787800 0x881f1c3e0e0f0f00

def z784 : W := mkw 0x0042802440000000 0x0008500488000000 0xe8e699fe7c070007 0xbd1cd33fcf80e000

def z785 : W := mkw 0x27dff76de106d000 0x04fbfeedbc20da00 0xe7fffffff0070003 0xfcfffffffe00e000

def z786 : W := mkw 0x04d2c02440000000 0x009a580488000000 0xe0fef9fe70000003 0xbc1fdf3fce000000

def z787 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xdff89ff00ff86787 0xfbff13fe01ff0cf0

def z788 : W := mkw 0x134fdfd005aed786 0x0269fbfa00b5daf0 0x0807fff00007ff83 0x0100fffe0000fff0

def z789 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0x57f81ff003f80782 0xcaff03fe007f00f0

def z790 : W := mkw 0x15b01c500ed00502 0x02b6038a01da00a0 0xc7f818700f800000 0xf8ff030e01f00000

def z791 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xfffffffff0008007 0xfffffffffe001000

def z792 : W := mkw 0x086288b65c6b6eed 0x610c5116cb8d6ddd 0xe8e699fe7c7f7e67 0xbd1cd33fcf8fefcc

def z793 : W := mkw 0x06b540000b56d000 0x00d6a800016ada00 0x9f19e0000ffff805 0xd3e33c0001ffff00

def z794 : W := mkw 0x15b83fdbbef92fff 0xa2b707fb77df25ff 0xfff9fffffff8ffff 0xffff3fffffff1fff

def z795 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0x60fffffff0000003 0x8c1ffffffe000000

def z796 : W := mkw 0x082008921f77f661 0x4104011243eefecc 0x080000000fe76664 0x0100000001fceccc

def z797 : W := mkw 0x2247c02d4106d000 0x0448f805a820da00 0x0807e00e0007f801 0x0100fc01c000ff00

def z798 : W := mkw 0x27dff76de18c899c 0xa4fbfeedbc319133 0xf7fffffff398999b 0xfefffffffe731333

def z799 : W := mkw 0x15b01c500ed00502 0x02b6038a01da00a0 0xc7e01e700f800002 0x78fc03ce01f00000

def z800 : W := mkw 0x07df976d40000000 0x00fbf2eda8000000 0xe7ff9ffff0000003 0xfcfff3fffe000000

def z801 : W := mkw 0x37dff76de0880186 0x06fbfeedbc110030 0xe7fffffff0000183 0xfcfffffffe000030

def z802 : W := mkw 0x0042802440000000 0x0008500488000000 0xf8e79ffff00087ff 0xff1cf3fffe0010ff

def z803 : W := mkw 0x05983f40a4800500 0x00b307e8149000a0 0xfff9fff1ff8087ff 0xffff3ffe3ff010ff

def z804 : W := mkw 0x279d7749a1048010 0x84f3aee934209002 0x0719660180008018 0x40e32cc030001003

def z805 : W := mkw 0x15b817d00af80386 0x02b702fa015f0070 0xd7f807f003f80786 0xdaff00fe007f00f0

def z806 : W := mkw 0x2128376deb56d000 0x042506edbd6ada00 0x38001ffffffff806 0x070003ffffffff00

def z807 : W := mkw 0x15b01cd00ef00702 0x02b6039a01de00e0 0xd7f819f00ff80606 0xfaff033e01ff00c0

def z808 : W := mkw 0x2247e02fe107d051 0x8448fc05fc20fa0a 0x2807e00ff007f879 0x0500fc01fe00ff0f

def z809 : W := mkw 0x15b01cd00ef80786 0x02b6039a01df00f0 0x47e018700f800780 0x28fc030e01f000f0

def z810 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0x67fff9fff0000001 0xacffff3ffe000000

def z811 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xe8e619fe7c070667 0x3d1cc33fcf80e0cc

def z812 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xe0e699fe7c070663 0xbc1cd33fcf80e0cc

def z813 : W := mkw 0x15b83fd0bef82fae 0x22b707fa17df05f5 0x67e01ff1ff8007fa 0x2cfc03fe3ff000ff

def z814 : W := mkw 0x15b83fd0bef82fae 0x22b707fa17df05f5 0xf7f9fff1fff87f87 0xfeff3ffe3fff0ff0

def z815 : W := mkw 0x15b01c500ed00502 0x02b6038a01da00a0 0x57f818700f980000 0x6aff030e01f30000

def z816 : W := mkw 0x0598174000000000 0x00b302e800000000 0xd7f81ff00f800006 0xfaff03fe01f00000

def z817 : W := mkw 0x0862802658436061 0x410c5004cb086c0c 0xe8e699fe7c676067 0xbd1cd33fcf8cec0c

def z818 : W := mkw 0x04b000000a500000 0x00960000014a0000 0xd7f819f00ff80006 0xfaff033e01ff0000

def z819 : W := mkw 0x0042802440000000 0x0008500488000000 0x40e699fe70000000 0xa81cd33fce000000

def z820 : W := mkw 0x15b81f500ed80586 0x02b703ea01db00b0 0xd7f81e700f980786 0x7aff03ce01f300f0

def z821 : W := mkw 0x06ffe380bb7efaac 0x20dffc70176fdf55 0x67e60781ff8707fa 0x2cfcc0f03ff0e0ff

def z822 : W := mkw 0x27d7f46de0000000 0x04fafe8dbc000000 0xe7e7f9fff0000003 0xbcfcff3ffe000000

def z823 : W := mkw 0x14b000500a500002 0x0296000a014a0000 0x47e000700f800000 0x28fc000e01f00000

def z824 : W := mkw 0x0042802440024000 0x0008500488004800 0xe8e699fe70076003 0xbd1cd33fce00ec00

def z825 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0xffe71fff8f8787ff 0xfffce3fff1f0f0ff

def z826 : W := mkw 0x15b03c50bed02d2a 0x22b6078a17da05a5 0x6fe1f871ff80f879 0x2dfc3f0e3ff01f0f

def z827 : W := mkw 0x05b81f400ed00500 0x00b703e801da00a0 0xd7f81ff00ff80786 0xfaff03fe01ff00f0

def z828 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xe8fff9fe7c676667 0xfd1fff3fcf8ceccc

def z829 : W := mkw 0x1598174002900102 0x02b302e800520020 0xc7f81ff003800002 0xf8ff03fe00700000

def z830 : W := mkw 0x2598376de0000000 0x04b306edbc000000 0xe7f9fffff0000003 0xfcff3ffffe000000

def z831 : W := mkw 0x1590144002900102 0x02b2028800520020 0x47e0187003800000 0x28fc030e00700000

def z832 : W := mkw 0x014a976440000000 0x002952ec88000000 0xe0e69ffe70000003 0xbc1cd3ffce000000

def z833 : W := mkw 0x2247e02ff105a879 0xa448fc05fe20b50f 0x2807e00ff007f879 0x0500fc01fe00ff0f

def z834 : W := mkw 0x159817c002b80386 0x02b302f800570070 0xd7f81ff003f80786 0xfaff03fe007f00f0

def z835 : W := mkw 0x04b82b90be782eac 0x2097057217cf05d5 0xfff9fff1fff8ffff 0xffff3ffe3fff1fff

def z836 : W := mkw 0x0225089b0d658651 0x8044a11361acb0ca 0xe8e719ff8c67867f 0xbd1ce33ff18cf0cf

def z837 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xf7fffffff0189803 0xfefffffffe031300

def z838 : W := mkw 0x14b823d0ba782aae 0x2297047a174f0555 0xdff9e1f07ff8f805 0xfbff3c3e0fff1f00

def z839 : W := mkw 0x082008921c636661 0x41040112438c6ccc 0x180000000c67e7fc 0x03000000018cfcff

def z840 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0x57f807f00ff80784 0xcaff00fe01ff00f0

def z841 : W := mkw 0x0a47a02ff107e879 0xe148f405fe20fd0f 0x2807e00ff007f879 0x0500fc01fe00ff0f

def z842 : W := mkw 0x15b81fd01ef82fae 0x22b703fa03df05f5 0xd7f81ff00ff87f86 0xfaff03fe01ff0ff0

def z843 : W := mkw 0x27dff76de008088c 0x24fbfeedbc010111 0xfffffffff0189fff 0xfffffffffe0313ff

def z844 : W := mkw 0x082008921d67f661 0x4104011243acfecc 0x080000000c67fe64 0x01000000018cffcc

def z845 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xf7fffffff0000787 0xfefffffffe0000f0

def z846 : W := mkw 0x079d3749a0000000 0x00f3a6e934000000 0xe7fffffff0000003 0xfcfffffffe000000

def z847 : W := mkw 0x279d7749a1049000 0x04f3aee934209200 0x0719660180009800 0x40e32cc030001300

def z848 : W := mkw 0x0042882644010441 0x00085104c8802088 0xe0e699fe7c070003 0xbc1cd33fcf80e000

def z849 : W := mkw 0x15b83fd0bef82fae 0x22b707fa17df05f5 0x47f8f9f07ff87800 0xa8ff1f3e0fff0f00

def z850 : W := mkw 0x03055c0b05859551 0x8060ab8160b0b2aa 0xbf077e0f8f879fff 0x77e0efc1f1f0f3ff

def z851 : W := mkw 0x27dff76de1048000 0x04fbfeedbc209000 0xe7ffffffff870003 0xfcfffffffff0e000

def z852 : W := mkw 0x14b823d0ba782aae 0x2297047a174f0555 0xfff9e7f1fff8ffff 0xffff3cfe3fff1fff

def z853 : W := mkw 0x2a47e02ff107f061 0x4548fc05fe20fe0c 0x2807e00ff007f861 0x0500fc01fe00ff0c

def z854 : W := mkw 0x0cfae3b4fa7a7aac 0x619f5c769f4f4f55 0x40f8e1f070787800 0x881f1c3e0e0f0f00

def z855 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xe7fe1ffff0000002 0xfcffc3fffe000000

def z856 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0x3f07060f8f8787fd 0x47e0e0c1f1f0f0ff

def z857 : W := mkw 0x05981f4004800500 0x00b303e8009000a0 0xc7f81ff00f800002 0xf8ff03fe01f00000

def z858 : W := mkw 0x37dff76de298098e 0x26fbfeedbc530131 0xf7fffffff398999b 0xfefffffffe731333

def z859 : W := mkw 0x186288b65efb6fef 0x630c5116cbdf6dfd 0xf8e699fe7fffffff 0xbf1cd33fcfffffff

def z860 : W := mkw 0x082008921c636661 0x41040112438c6ccc 0x000000000c676000 0x00000000018cec00

def z861 : W := mkw 0x15b83fd0aef80f8e 0x22b707fa15df01f1 0xd7f87ff00ff81f86 0xfaff0ffe01ff03f0

def z862 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0xffffe1807ffff807 0xfffffc300fffff00

def z863 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xd7f91ff18ff8879e 0xfaff23fe31ff10f3

def z864 : W := mkw 0x24d2c06440000000 0x049a580c88000000 0xe0e699fe70000003 0xbc1cd33fce000000

def z865 : W := mkw 0x0042802440000000 0x0008500488000000 0x60e619fe70000002 0x2c1cc33fce000000

def z866 : W := mkw 0x00082380b0282aac 0x2001047016050555 0xbf19e781fff8ffff 0xf7e33cf03fff1fff

def z867 : W := mkw 0x082008921e737661 0x4104011243ce6ecc 0x080000000c7f7e64 0x01000000018fefcc

def z868 : W := mkw 0x15b83fd2bef92fef 0x22b707fa57df25fd 0xffffffffffffffff 0xffffffffffffffff

def z869 : W := mkw 0x1db81fd21efb67e7 0x43b703fa43df6cfc 0xfff89ff07fff67e7 0xffff13fe0fffecfc

def z870 : W := mkw 0x0042802440000000 0x0008500488000000 0x60e099fe70000002 0x8c1c133fce000000

def z871 : W := mkw 0x0042802440000000 0x0008500488000000 0xe0fff9fe70000003 0xfc1fff3fce000000

def z872 : W := mkw 0x27dff76de3149000 0x04fbfeedbc629200 0xffffffffff9f9807 0xfffffffffff3f300

def z873 : W := mkw 0x082008921ce36761 0x41040112439c6cec 0x180000000fe767e4 0x0300000001fcecfc

def z874 : W := mkw 0x020d2380b12caaac 0x2041a47016259555 0xbf070781ff8787ff 0x77e0e0f03ff0f0ff

def z875 : W := mkw 0x04b000000b56d000 0x00960000016ada00 0xdff9e0000ffff805 0xfbff3c0001ffff00

def z876 : W := mkw 0x15b83fd0bef82fae 0x22b707fa17df05f5 0xdff97ff18ff8fffe 0xfbff2ffe31ff1fff

def z877 : W := mkw 0x0247c0244106d000 0x0048f8048820da00 0x2807e00e7007f801 0x0500fc01ce00ff00

def z878 : W := mkw 0x15983740a298098e 0x22b306e814530131 0xf7f9fff1f398999b 0xfeff3ffe3e731333

def z879 : W := mkw 0x214ab76de0000000 0x042956edbc000000 0x60e61ffff0000002 0x2c1cc3fffe000000

def z880 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0x5fff60000ffff804 0x6bffec0001ffff00

def z881 : W := mkw 0x15b01cd00ef00702 0x02b6039a01de00e0 0x47e019f00f800602 0x28fc033e01f000c0

def z882 : W := mkw 0x27d7d46d40000000 0x04fafa8da8000000 0x67e619fe70000002 0x2cfcc33fce000000

def z883 : W := mkw 0x01283f90bce82fac 0x202507f2179d05f5 0xfff9fff1fff8ffff 0xffff3ffe3fff1fff

def z884 : W := mkw 0x004aa324e0000000 0x000954649c000000 0xe0fef9fe70000003 0xbc1fdf3fce000000

def z885 : W := mkw 0x0347942d41848110 0x8068f285a8309022 0xf7e79ffff380819b 0xfefcf3fffe701033

def z886 : W := mkw 0x0b6794bd59e6e330 0xc16cf297ab3cdc66 0x57e187f1f3e0e198 0xcafc30fe3e7c1c33

def z887 : W := mkw 0x082008921c636661 0x41040112438c6ccc 0xa80000000c676667 0x15000000018ceccc

def z888 : W := mkw 0x0062802448424000 0x000c500489084800 0xe0e699fe7c070003 0xbc1cd33fcf80e000

def z889 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0xfffff80e0ffff807 0xffffff01c1ffff00

def z890 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0xffffe0018ffff87d 0xfffffc0031ffff0f

def z891 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0x68e699fe70676663 0x8d1cd33fce0ceccc

def z892 : W := mkw 0x0247c0244106d000 0x0048f8048820da00 0xe8e7f9fe7007f803 0xbd1cff3fce00ff00

def z893 : W := mkw 0x27dff76de0024000 0x04fbfeedbc004800 0xeffffffff0076003 0xfdfffffffe00ec00

def z894 : W := mkw 0x2108376de0000000 0x042106edbc000000 0xe0e01ffff0000002 0xbc1c03fffe000000

def z895 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0x1f071e0f8f8787fc 0x63e0e3c1f1f0f0ff

def z896 : W := mkw 0x27dff76de0000808 0x24fbfeedbc000101 0xe7fffffff000981b 0xfcfffffffe001303

def z897 : W := mkw 0x27dff76de106d000 0x04fbfeedbc20da00 0xffffffffff87f807 0xfffffffffff0ff00

def z898 : W := mkw 0x1db81fd20efb47c7 0x43b703fa41df68f8 0xd7f81ff00fff0786 0xfaff03fe01ffe0f0

def z899 : W := mkw 0x04b008901e702620 0x0096011203ce04c4 0xfff9f9f07ff8fe67 0xffff3f3e0fff1fcc

def z900 : W := mkw 0x27dff76de1048010 0x84fbfeedbc209002 0xe7fffffff000801b 0xfcfffffffe001003

def z901 : W := mkw 0x04d2802440000000 0x009a500488000000 0xe7fe99fe70000003 0xfcffd33fce000000

def z902 : W := mkw 0x0205000b01058051 0x8040a0016020b00a 0xbf07060f8f8787ff 0x77e0e0c1f1f0f0ff

def z903 : W := mkw 0x15981fd006b80786 0x02b303fa00d700f0 0xd7f81ff003980782 0xfaff03fe007300f0

def z904 : W := mkw 0x15981f4006980586 0x02b303e800d300b0 0xd7f81ff00f980786 0xfaff03fe01f300f0

def z905 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0xdfffe0000ffffffd 0xfbfffc0001ffffff

def z906 : W := mkw 0x086288364c434441 0x410c5106c9886888 0xe8e699fe7c676007 0xbd1cd33fcf8cec00

def z907 : W := mkw 0x0042a024e0000000 0x000854049c000000 0xe0e7f9fff0000003 0xbc1cff3ffe000000

def z908 : W := mkw 0x37dff76de39c8196 0x86fbfeedbc739032 0xf7fffffff398819b 0xfefffffffe731033

def z909 : W := mkw 0x27dff76de0800110 0x84fbfeedbc100022 0xe7fffffff000019b 0xfcfffffffe000033

def z910 : W := mkw 0x0e9548b65735b661 0x41d2a916cae6b6cc 0x371979fe73989e62 0x46e32f3fce7313cc

def z911 : W := mkw 0x15b83fd0bef82fae 0x22b707fa17df05f5 0xfff8fff07ff87fe7 0xffff1ffe0fff0ffc

def z912 : W := mkw 0x15b81fd01ef827a6 0x02b703fa03df04f4 0xfff99ff1fff8e7ff 0xffff33fe3fff1cff

def z913 : W := mkw 0x00082380b0282aac 0x2001047016050555 0xb81fe781fc7fffff 0xf703fcf03f8fffff

def z914 : W := mkw 0x279d7749a3949110 0x84f3aee934729222 0x1719660183989998 0x42e32cc030731333

def z915 : W := mkw 0x182008921efb6fef 0x6304011243df6dfd 0x180000000ffffffc 0x0300000001ffffff

def z916 : W := mkw 0x15b01cd00ef00702 0x02b6039a01de00e0 0x47e019f00fe00000 0xa8fc033e01fc0000

def z917 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0xc7ffe0000fff7801 0xf8fffc0001ffef00

def z918 : W := mkw 0x19083ff6f4a92fef 0x632107fede9525fd 0x20001ffff00007fa 0x040003fffe0000ff

def z919 : W := mkw 0x279d7749a1048000 0x04f3aee934209000 0x1719660183808000 0x42e32cc030701000

def z920 : W := mkw 0x379d7749a39c9186 0x06f3aee934739230 0x1719660183989980 0x42e32cc030731330

def z921 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xc7e01ff00fe00786 0xb8fc03fe01fc00f0

def z922 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xf7fffffff000819b 0xfefffffffe001033

def z923 : W := mkw 0x15b81f500ed00502 0x02b703ea01da00a0 0xd7f81ff00ff80006 0xfaff03fe01ff0000

def z924 : W := mkw 0x04b008100e500400 0x0096010201ca0080 0xd7f818700ff80004 0xfaff030e01ff0000

def z925 : W := mkw 0x15b81f500ed80586 0x02b703ea01db00b0 0x47e01e700f800180 0x28fc03ce01f00030

def z926 : W := mkw 0x1db81fd01efa67a6 0x43b703fa03df4cf4 0xd7f81ff00ff86786 0xfaff03fe01ff0cf0

def z927 : W := mkw 0x15b83fd0aef80786 0x02b707fa15df00f0 0xfff9fff1fff887ff 0xffff3ffe3fff10ff

def z928 : W := mkw 0x086288b65e736661 0x410c5116cbce6ccc 0xf8e699fe7fff6667 0xbf1cd33fcfffeccc

def z929 : W := mkw 0x0247802f41058051 0x8048f005e820b00a 0x2807800ff0078079 0x0500f001fe00f00f

def z930 : W := mkw 0x15b81fdb0ef907d7 0x82b703fb61df20fa 0xd7f81ffe0ff80786 0xfaff03ffc1ff00f0

def z931 : W := mkw 0x14b803d00a780286 0x0297007a014f0050 0x57f801f003f80000 0xcaff003e007f0000

def z932 : W := mkw 0x2247e02de1049000 0x0448fc05bc209200 0x2007e00ff0009801 0x0400fc01fe001300

def z933 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xffe699fe7fe76667 0xfffcd33fcffceccc

def z934 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0x57f819f00ff80784 0xaaff033e01ff00f0

def z935 : W := mkw 0x2fbd7fdbbc636661 0x45f7affb778c6ccc 0x0f1966018c676664 0x41e32cc0318ceccc

def z936 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0xffffe6018ffff807 0xfffffcc031ffff00

def z937 : W := mkw 0x01201c100cc00500 0x00240382019800a0 0xd7e01e700f800786 0x7afc03ce01f000f0

def z938 : W := mkw 0x14b80bd00e780686 0x0297017a01cf00d0 0xd7f819f00ff80606 0xfaff033e01ff00c0

def z939 : W := mkw 0x182008921e7b66e7 0x4304011243cf6cdc 0x080000000c7f6664 0x01000000018feccc

def z940 : W := mkw 0x2247e02fe1058051 0x8448fc05fc20b00a 0x2007e00ff0070001 0x0400fc01fe00e000

def z941 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xfffffffff078ffff 0xfffffffffe0f1fff

def z942 : W := mkw 0x0598174002100000 0x00b302e800420000 0xd7f81ff003980002 0xfaff03fe00730000

def z943 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0x57e01ff00ff80786 0x2afc03fe01ff00f0

def z944 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xdff81ff00ff887fe 0xfbff03fe01ff10ff

def z945 : W := mkw 0x25daf76de0000000 0x04bb5eedbc000000 0xe0f9fffff0000003 0xdc1f3ffffe000000

def z946 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0xdfffe6000fffff87 0xfbfffcc001fffff0

def z947 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0x3f061e0f8f8787fe 0x27e0c3c1f1f0f0ff

def z948 : W := mkw 0x279d7749a18c899c 0xa4f3aee934319133 0x1719660183989998 0x42e32cc030731333

def z949 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xc8e699fe7c676005 0xb91cd33fcf8cec00

def z950 : W := mkw 0x27dff76de1048000 0x04fbfeedbc209000 0xeffffffff0078003 0xfdfffffffe00f000

def z951 : W := mkw 0x022500000b56d000 0x0044a000016ada00 0x9f1fe0000ffff805 0xf3e3fc0001ffff00

def z952 : W := mkw 0x086288364c434441 0x410c5106c9886888 0xe8e699fe7c070667 0xbd1cd33fcf80e0cc

def z953 : W := mkw 0x27dfd76d40000000 0x04fbfaeda8000000 0xe7fe9ffe70000003 0xfcffd3ffce000000

def z954 : W := mkw 0x15b81fd21ef927e7 0x02b703fa43df24fc 0xfffe9ffe7fff67e7 0xffffd3ffcfffecfc

def z955 : W := mkw 0x082008921ce36771 0xc1040112439c6cee 0x080000000c6767fc 0x01000000018cecff

def z956 : W := mkw 0x182008921ceb67e7 0x43040112439d6cfc 0x080000000c6767e4 0x01000000018cecfc

def z957 : W := mkw 0x15b837d0baf82bae 0x22b706fa175f0575 0x57f9e7f1f3f8f998 0xcaff3cfe3e7f1f33

def z958 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xe7e71ffff0000003 0x7cfce3fffe000000

def z959 : W := mkw 0x2247e02de1048000 0x0448fc05bc209000 0x2807e00ff0078001 0x0500fc01fe00f000

def z960 : W := mkw 0x2247c02f41058051 0x8448f805e820b00a 0x0006000e00070000 0x0000c001c000e000

def z961 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xf8e699fe7c7ffe67 0xbf1cd33fcf8fffcc

def z962 : W := mkw 0x15b01c500ed80586 0x02b6038a01db00b0 0x57e018700f980180 0x2afc030e01f30030

def z963 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xd7f819f00ff80004 0xfaff033e01ff0000

def z964 : W := mkw 0x15b817d00a780286 0x02b702fa014f0050 0xd7f81ff00ff80006 0xfaff03fe01ff0000

def z965 : W := mkw 0x25daf76de0000000 0x04bb5eedbc000000 0xe0fefffff0000003 0xbc1fdffffe000000

def z966 : W := mkw 0x00002000b0002828 0x2000040016000505 0xb819e601f078ffff 0xd7033cc03e0f1fff

def z967 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0xbf079f8fff8787ff 0xf7e0f3f1fff0f0ff

def z968 : W := mkw 0x082008921c636661 0x41040112438c6ccc 0x9819e0000c7ffe65 0xd3033c00018fffcc

def z969 : W := mkw 0x11281fd00ce80786 0x022503fa019d00f0 0xd7e01ff00fe00786 0xfafc03fe01fc00f0

def z970 : W := mkw 0x15b817d00af80386 0x02b702fa015f0070 0xd7f81ff003f80182 0xfaff03fe007f0030

def z971 : W := mkw 0x0a47802f4107c051 0xc148f005e820f80a 0x0006000e00070000 0x0000c001c000e000

def z972 : W := mkw 0x11201c900ef80786 0x0224039201df00f0 0xd7e01ff00ff80786 0xfafc03fe01ff00f0

def z973 : W := mkw 0x15b83fd0bef82fae 0x22b707fa17df05f5 0xf7f97ff1fff89ffe 0xfeff2ffe3fff13ff

def z974 : W := mkw 0x15b83fd0aef80f8e 0x22b707fa15df01f1 0xf7f9fff1fff89f9f 0xfeff3ffe3fff13f3

def z975 : W := mkw 0x15b81f500ed00502 0x02b703ea01da00a0 0x47f819f00f800000 0xa8ff033e01f00000

def z976 : W := mkw 0x082008921c636e69 0x61040112438c6dcd 0x080000000c67fe7c 0x01000000018cffcf

def z977 : W := mkw 0x14b803d00a780286 0x0297007a014f0050 0xd7f807f00ff80786 0xfaff00fe01ff00f0

def z978 : W := mkw 0x14b80bd00ef80786 0x0297017a01df00f0 0xd7f801f00ff80784 0xfaff003e01ff00f0

def z979 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xf7f81ff18ff807fe 0xfeff03fe31ff00ff

def z980 : W := mkw 0x004a832440000000 0x0009506488000000 0xe0fe9ffe70000003 0xfc1fd3ffce000000

def z981 : W := mkw 0x086288b64c634641 0x410c5116c98c68c8 0xe0e699fe7c670607 0xbc1cd33fcf8ce0c0

def z982 : W := mkw 0x086288b65c6b66e5 0x410c5116cb8d6cdc 0xf8e699fe7c7f67e7 0xbf1cd33fcf8fecfc

def z983 : W := mkw 0x086280b658636261 0x410c5016cb0c6c4c 0xe8e699fe70676063 0xbd1cd33fce0cec0c

def z984 : W := mkw 0x24dae364e0000000 0x049b5c6c9c000000 0x60f8f9fe70000002 0x8c1f1f3fce000000

def z985 : W := mkw 0x279d376de0000000 0x04f3a6edbc000000 0xe7ff1ffff0000003 0xfcffe3fffe000000

def z986 : W := mkw 0x224fe3aff12daafd 0xa449fc75fe25b55f 0xb81fe78ff07fffff 0xd703fcf1fe0fffff

def z987 : W := mkw 0x15b01c500ed00502 0x02b6038a01da00a0 0x57e018700f800784 0x2afc030e01f000f0

def z988 : W := mkw 0x05b837c0ba782aac 0x20b706f8174f0555 0xfff9fff1fff8ffff 0xffff3ffe3fff1fff

def z989 : W := mkw 0x0a47e026f107f869 0x6148fc04de20ff0d 0x2807e00ff007f879 0x0500fc01fe00ff0f

def z990 : W := mkw 0x15b81fd20ef907c7 0x02b703fa41df20f8 0xd7fe1ffe0fff0786 0xfaffc3ffc1ffe0f0

def z991 : W := mkw 0x06d7c02440000000 0x00daf80488000000 0xe7e699fe70000003 0xbcfcd33fce000000

def z992 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0x67ff7ffff0000002 0x6cffeffffe000000

def z993 : W := mkw 0x06dfe324e0000000 0x00dbfc649c000000 0xe7fffffff0000003 0xfcfffffffe000000

def z994 : W := mkw 0x15b01c500ed00502 0x02b6038a01da00a0 0x47f818700ff80000 0xa8ff030e01ff0000

def z995 : W := mkw 0x27dff76de1048000 0x04fbfeedbc209000 0xffffffffff8787ff 0xfffffffffff0f0ff

def z996 : W := mkw 0x01001c0204810541 0x00200380409020a8 0xbf071e0f8f8787ff 0x77e0e3c1f1f0f0ff

def z997 : W := mkw 0x25daf76de0000000 0x04bb5eedbc000000 0x40f8f9fe70000000 0x881f1f3fce000000

def z998 : W := mkw 0x06f7c0090b56d010 0x80def801216ada02 0xdfffe0018ffff81d 0xfbfffc0031ffff03

def z999 : W := mkw 0x01001c0004800500 0x00200380009000a0 0xd7e01ff00f800786 0xfafc03fe01f000f0

def z1000 : W := mkw 0x00082380b0282aac 0x2001047016050555 0xf8f9fff1f078ffff 0xff1f3ffe3e0f1fff

def z1001 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0xcffee0000fff7805 0xb9ffdc0001ffef00

def z1002 : W := mkw 0x2347f42de0000000 0x0468fe85bc000000 0xe7e7fffff0000003 0xfcfcfffffe000000

def z1003 : W := mkw 0x0042802440000000 0x0008500488000000 0xe0e79ffff0000003 0xfc1cf3fffe000000

def z1004 : W := mkw 0x2142946d40000000 0x0428528da8000000 0xe0e699fe70000003 0xbc1cd33fce000000

def z1005 : W := mkw 0x27f7dc6f4fd7d551 0x84fefb8de9fafaaa 0x47e6187e0f870000 0x28fcc30fc1f0e000

def z1006 : W := mkw 0x15b81fd01ef827a6 0x02b703fa03df04f4 0xdff81ff00ff867e6 0xfbff03fe01ff0cfc

def z1007 : W := mkw 0x004aa324e008088c 0x200954649c010111 0xf0fffffff018999b 0xfe1ffffffe031333

def z1008 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0x47e619fe70000000 0x28fcc33fce000000

def z1009 : W := mkw 0x15b817d00af80386 0x02b702fa015f0070 0xd7f807f00ff80184 0xfaff00fe01ff0030

def z1010 : W := mkw 0x002008900c600600 0x00040112018c00c0 0xd7e019f00fe00606 0xfafc033e01fc00c0

def z1011 : W := mkw 0x082008921ff7f771 0xc104011243fefeee 0x180000000ffffffc 0x0300000001ffffff

def z1012 : W := mkw 0x082008921de7e771 0xc104011243bcfcee 0x080000000fe76664 0x0100000001fceccc

def z1013 : W := mkw 0x279d776de0000000 0x04f3aeedbc000000 0xe7f97ffff0000002 0xfcff2ffffe000000

def z1014 : W := mkw 0x186288b65ef36763 0x430c5116cbde6cec 0xe8e699fe7fe76667 0xbd1cd33fcffceccc

def z1015 : W := mkw 0x0a2508921d67e661 0x4144a11243acfccc 0x9f0700000fe7e665 0x73e0e00001fcfccc

def z1016 : W := mkw 0x0142942440000000 0x0028528488000000 0xe7e69ffe70000003 0xfcfcd3ffce000000

def z1017 : W := mkw 0x04b80b900e780684 0x0097017201cf00d0 0xd7f81ff00ff80786 0xfaff03fe01ff00f0

def z1018 : W := mkw 0x082008921c636661 0x41040112438c6ccc 0x180000000c7ffe64 0x03000000018fffcc

def z1019 : W := mkw 0x0a47802f5107e071 0xc148f005ea20fc0e 0x2806800e70076061 0x0500d001ce00ec0c

def z1020 : W := mkw 0x37dff76de2900102 0x06fbfeedbc520020 0xe7fffffff3800003 0xfcfffffffe700000

def z1021 : W := mkw 0x0142942d40000000 0x00285285a8000000 0xe0e69ffff0000003 0xbc1cd3fffe000000

def z1022 : W := mkw 0x24dae364e0000000 0x049b5c6c9c000000 0x40fef9fe70000000 0xa81fdf3fce000000

def z1023 : W := mkw 0x35b83fd9aef80786 0x06b707fb35df00f0 0xd7f81ff18ff80786 0xfaff03fe31ff00f0

def z1024 : W := mkw 0x08282b92bc6b6eed 0x61050572578d6ddd 0x181966018c7ffffc 0x43032cc0318fffff

def z1025 : W := mkw 0x05b81fd00e700600 0x00b703fa01ce00c0 0xd7f81ff00ff80606 0xfaff03fe01ff00c0

def z1026 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xf8fffffffc7fffff 0xff1fffffff8fffff

def z1027 : W := mkw 0x00082380b0282aac 0x2001047016050555 0x3819e601f078fffd 0x47033cc03e0f1fff

def z1028 : W := mkw 0x0347942d40000000 0x0068f285a8000000 0xe7e699fe70000003 0xbcfcd33fce000000

def z1029 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0x57f81ff00f980782 0x6aff03fe01f300f0

def z1030 : W := mkw 0x15b83fd0bef82fae 0x22b707fa17df05f5 0xfff81ff1fff8fffe 0xffff03fe3fff1fff

def z1031 : W := mkw 0x086288364c434441 0x410c5106c9886888 0x60e619fe7c070002 0x2c1cc33fcf80e000

def z1032 : W := mkw 0x034fb72de0000000 0x0069f6e5bc000000 0xe7fffffff0000003 0xfcfffffffe000000

def z1033 : W := mkw 0x27dff76de106d000 0x04fbfeedbc20da00 0xfffffffff07ff807 0xfffffffffe0fff00

def z1034 : W := mkw 0x186288b65e7b66e7 0x430c5116cbcf6cdc 0xe8e699fe7c7f6667 0xbd1cd33fcf8feccc

def z1035 : W := mkw 0x086288b65ce36761 0x410c5116cb9c6cec 0xf8e699fe7fe767e7 0xbf1cd33fcffcecfc

def z1036 : W := mkw 0x15b01cd00ef80786 0x02b6039a01df00f0 0xd7e019f00ff80786 0xbafc033e01ff00f0

def z1037 : W := mkw 0x15b83fd0bef82fae 0x22b707fa17df05f5 0xd7f9fff1fff8ff9e 0xfaff3ffe3fff1ff3

def z1038 : W := mkw 0x04b000900a700200 0x00960012014e0040 0xd7f801f00ff80004 0xfaff003e01ff0000

def z1039 : W := mkw 0x2042a02de0000000 0x04085405bc000000 0xe0e699fff0000003 0xbc1cd33ffe000000

def z1040 : W := mkw 0x1db01c520ed34543 0x43b6038a41da68a8 0x47e018700f870000 0x28fc030e01f0e000

def z1041 : W := mkw 0x279d7749a1848110 0x84f3aee934309022 0x0719660183800000 0x40e32cc030700000

def z1042 : W := mkw 0x182008921fffe7f7 0xc304011243fffcfe 0x180000000fffe7fc 0x0300000001fffcff

def z1043 : W := mkw 0x15b83f50aed00502 0x02b707ea15da00a0 0xe7f9fff1ff800003 0xfcff3ffe3ff00000

def z1044 : W := mkw 0x09429c2654836561 0x41285384ca906cac 0xbf069e0e7f8767e7 0x77e0d3c1cff0ecfc

def z1045 : W := mkw 0x15b83fd0bef82fae 0x22b707fa17df05f5 0xdff8fff07ff8fffe 0xfbff1ffe0fff1fff

def z1046 : W := mkw 0x026780000946c000 0x004cf0000128d800 0xdfffe0000ffff805 0xfbfffc0001ffff00

def z1047 : W := mkw 0x05d2946440000000 0x00ba528c88000000 0xe7e699fe70000003 0xbcfcd33fce000000

def z1048 : W := mkw 0x27dff76de0025000 0x04fbfeedbc004a00 0xe7fffffff0007803 0xfcfffffffe000f00

def z1049 : W := mkw 0x05983fc0b4a82fac 0x20b307f8169505f5 0xfff9fff1fff8ffff 0xffff3ffe3fff1fff

def z1050 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0x37071e0f8f8787fa 0x66e0e3c1f1f0f0ff

def z1051 : W := mkw 0x14b008900ef80786 0x0296011201df00f0 0xd7f819f00ff80786 0xfaff033e01ff00f0

def z1052 : W := mkw 0x234ff76de0000000 0x0469feedbc000000 0xe0e7fffff0000003 0xbc1cfffffe000000

def z1053 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0x57f81e700ff80784 0x6aff03ce01ff00f0

def z1054 : W := mkw 0x26f7c0644b56d000 0x04def80c896ada00 0xdfffe0700ffff805 0xfbfffc0e01ffff00

def z1055 : W := mkw 0x24dae364e0000000 0x049b5c6c9c000000 0xe0fffffff0000003 0xfc1ffffffe000000

def z1056 : W := mkw 0x15b83fd0bef82fae 0x22b707fa17df05f5 0xfff91ff1fff887ff 0xffff23fe3fff10ff

def z1057 : W := mkw 0x0842882654036461 0x41085104ca806c8c 0xe8e699fe7c076667 0xbd1cd33fcf80eccc

def z1058 : W := mkw 0x15b01cd00ef00702 0x02b6039a01de00e0 0x47e018700fe00604 0x28fc030e01fc00c0

def z1059 : W := mkw 0x15b81fd01ef827a6 0x02b703fa03df04f4 0xf7f81ff07ff807e6 0xfeff03fe0fff00fc

def z1060 : W := mkw 0x0695400003149000 0x00d2a80000629200 0x9f1fe0000ffff805 0xf3e3fc0001ffff00

def z1061 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0xaf061e0f8f8707ff 0x35e0c3c1f1f0e0ff

def z1062 : W := mkw 0x15b81f500ed00502 0x02b703ea01da00a0 0x47e01ff00f800002 0x28fc03fe01f00000

def z1063 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xf8e799fe7c67e667 0xff1cf33fcf8cfccc

def z1064 : W := mkw 0x082008921c636661 0x41040112438c6ccc 0x880080000c676665 0x91001000018ceccc

def z1065 : W := mkw 0x0205080205058441 0x0040a10040a0b088 0xbf071e0f8f8787ff 0x77e0e3c1f1f0f0ff

def z1066 : W := mkw 0x004288a654212661 0x00085114ca8424cc 0xe8e699fe7c676667 0xbd1cd33fcf8ceccc

def z1067 : W := mkw 0x06b500000b548000 0x00d6a000016a9000 0xdfffe0000ffff805 0xfbfffc0001ffff00

def z1068 : W := mkw 0x25daf764e0000000 0x04bb5eec9c000000 0xe7fefffe70000003 0xfcffdfffce000000

def z1069 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0x57f81ff00ff80180 0xeaff03fe01ff0030

def z1070 : W := mkw 0x082008921c6b6eed 0x61040112438d6ddd 0x080000000c6767fc 0x01000000018cecff

def z1071 : W := mkw 0x05b014400a500000 0x00b60288014a0000 0xd7f818700ff80004 0xfaff030e01ff0000

def z1072 : W := mkw 0x182008921ef927e7 0x4304011243df24fc 0x100000000ff807e4 0x0200000001ff00fc

def z1073 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xf7fffffff0780007 0xfefffffffe0f0000

def z1074 : W := mkw 0x27dff76de3149000 0x04fbfeedbc629200 0xfffffffff3f8f807 0xfffffffffe7f1f00

def z1075 : W := mkw 0x0a4fa3aff12feafd 0xe149f475fe25fd5f 0xb81fe78ff07fffff 0xd703fcf1fe0fffff

def z1076 : W := mkw 0x06f7c0244b56d000 0x00def804896ada00 0xdffff87e0ffff805 0xfbffff0fc1ffff00

def z1077 : W := mkw 0x14b000500a500002 0x0296000a014a0000 0xd7f800700ff80004 0xfaff000e01ff0000

def z1078 : W := mkw 0x27dff76de1848110 0x84fbfeedbc309022 0xe7fffffff3800003 0xfcfffffffe700000

def z1079 : W := mkw 0x0842802640034041 0x41085004c8006808 0xe0e699fe70070003 0xbc1cd33fce00e000

def z1080 : W := mkw 0x15b01c500ed00502 0x02b6038a01da00a0 0xc7e019f00f800002 0xb8fc033e01f00000

def z1081 : W := mkw 0x06f7c0244b56d000 0x00def804896ada00 0xdfffe1f07ffff805 0xfbfffc3e0fffff00

def z1082 : W := mkw 0x04f2c0000b56d000 0x009e5800016ada00 0xdff8e0000ffff804 0xfbff1c0001ffff00

def z1083 : W := mkw 0x15b83fd0bef827a6 0x02b707fa17df04f4 0xfff9fff1fff867e7 0xffff3ffe3fff0cfc

def z1084 : W := mkw 0x04b008900e700600 0x0096011201ce00c0 0xc7e019f00fe00606 0xb8fc033e01fc00c0

def z1085 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xc7f81ff00f800782 0xf8ff03fe01f000f0

def z1086 : W := mkw 0x27dff76de2100000 0x04fbfeedbc420000 0xf7fffffff3980003 0xfefffffffe730000

def z1087 : W := mkw 0x05dab764e0000000 0x00bb56ec9c000000 0xe7fffffff0000003 0xfcfffffffe000000

def z1088 : W := mkw 0x27dff76de31c988c 0x24fbfeedbc639311 0xf7fffffff398999b 0xfefffffffe731333

def z1089 : W := mkw 0x15b01c500ed00502 0x02b6038a01da00a0 0xd7e018700f800004 0x7afc030e01f00000

def z1090 : W := mkw 0x084288b654212661 0x41085116ca8424cc 0xe8e699fe7c070667 0xbd1cd33fcf80e0cc

def z1091 : W := mkw 0x27d7d46d40000000 0x04fafa8da8000000 0xe7e79ffff0000003 0xfcfcf3fffe000000

def z1092 : W := mkw 0x279d7749a31c988c 0x24f3aee934639311 0x1719660183989998 0x42e32cc030731333

def z1093 : W := mkw 0x05b01c900ef00700 0x00b6039201de00e0 0xd7f81ff00ff80786 0xfaff03fe01ff00f0

def z1094 : W := mkw 0x086288b65c6b6eed 0x610c5116cb8d6ddd 0xf8e79ffffc7fffff 0xff1cf3ffff8fffff

def z1095 : W := mkw 0x01281f900ce80784 0x002503f2019d00f0 0xd7f81ff00ff80786 0xfaff03fe01ff00f0

def z1096 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0x47e019f00f800000 0x28fc033e01f00000

def z1097 : W := mkw 0x07d7d42d40000000 0x00fafa85a8000000 0xe7fffffff0000003 0xfcfffffffe000000

def z1098 : W := mkw 0x214ab76de0000000 0x042956edbc000000 0x60e09ffff0000002 0x8c1c13fffe000000

def z1099 : W := mkw 0x15b817400ad80186 0x02b702e8015b0030 0xd7f81ff00ff80186 0xfaff03fe01ff0030

def z1100 : W := mkw 0x006280a458626220 0x000c50148b0c4c44 0xe8e699fe7c676667 0xbd1cd33fcf8ceccc

def z1101 : W := mkw 0x04f280000a524000 0x009e5000014a4800 0xdfffe0000ffff805 0xfbfffc0001ffff00

def z1102 : W := mkw 0x27dff76de2101000 0x04fbfeedbc420200 0xe7fffffff0181803 0xfcfffffffe030300

def z1103 : W := mkw 0x15981fd004a80786 0x02b303fa009500f0 0xd7f81ff00f800786 0xfaff03fe01f000f0

def z1104 : W := mkw 0x27dff76de0800100 0x04fbfeedbc100020 0xf7fffffff3800183 0xfefffffffe700030

def z1105 : W := mkw 0x15b83fd0bef82fae 0x22b707fa17df05f5 0xf7f9fff1fff807ff 0xfeff3ffe3fff00ff

def z1106 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xc0e699fe7c676606 0xb81cd33fcf8cecc0

def z1107 : W := mkw 0x2598376de0000000 0x04b306edbc000000 0x67e01ffff0000002 0x2cfc03fffe000000

def z1108 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xeffffffff0000667 0xfdfffffffe0000cc

def z1109 : W := mkw 0x0a47c0264107d041 0x4148f804c820fa08 0x0006000e00070000 0x0000c001c000e000

def z1110 : W := mkw 0x27dff76de1049000 0x04fbfeedbc209200 0xe7fffffff0009803 0xfcfffffffe001300

def z1111 : W := mkw 0x0a4780265107e061 0x4148f004ca20fc0c 0x2807800e7007e061 0x0500f001ce00fc0c

def z1112 : W := mkw 0x279d7749a3149000 0x04f3aee934629200 0x0719660183800000 0x40e32cc030700000

def z1113 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xfff9fff18ff8ffff 0xffff3ffe31ff1fff

def z1114 : W := mkw 0x15b83fd0aef80786 0x02b707fa15df00f0 0xd7f97ff18ff80786 0xfaff2ffe31ff00f0

def z1115 : W := mkw 0x214ab76de0000000 0x042956edbc000000 0xe0fffffff0000003 0xfc1ffffffe000000

def z1116 : W := mkw 0x086288b65e737661 0x410c5116cbce6ecc 0xe8e699fe7c7f7e67 0xbd1cd33fcf8fefcc

def z1117 : W := mkw 0x15b01cd00ef00702 0x02b6039a01de00e0 0xd7e01ff00fe00786 0xfafc03fe01fc00f0

def z1118 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xf8fe99fe7c7f6667 0xff1fd33fcf8feccc

def z1119 : W := mkw 0x15b01c520ed10543 0x02b6038a41da20a8 0xefe6187e0f870667 0x3dfcc30fc1f0e0cc

def z1120 : W := mkw 0x204aa364e0000000 0x0409546c9c000000 0xe0e699fe70000003 0xbc1cd33fce000000

def z1121 : W := mkw 0x15b01cd00ef80786 0x02b6039a01df00f0 0x47e018700ff80000 0x28fc030e01ff0000

def z1122 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xc7fefffe70000002 0xf8ffdfffce000000

def z1123 : W := mkw 0x27d7d46d40000000 0x04fafa8da8000000 0xe7fff9fe70000003 0xfcffff3fce000000

def z1124 : W := mkw 0x37dff76de39c9186 0x06fbfeedbc739230 0xf7fffffff3989983 0xfefffffffe731330

def z1125 : W := mkw 0x15b01c500ed00502 0x02b6038a01da00a0 0x57e01e700f800180 0x6afc03ce01f00030

def z1126 : W := mkw 0x002008921c612661 0x00040112438c24cc 0xe8e699fe7c676667 0xbd1cd33fcf8ceccc

def z1127 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xe8e69ffffc6767ff 0xbd1cd3ffff8cecff

def z1128 : W := mkw 0x15b81fd20ef907c7 0x02b703fa41df20f8 0xdff81ff00fff07e6 0xfbff03fe01ffe0fc

def z1129 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0x68e699fe7c676061 0xad1cd33fcf8cec0c

def z1130 : W := mkw 0x179d3749a39c899e 0xa2f3a6e934739133 0x1719660183989998 0x42e32cc030731333

def z1131 : W := mkw 0x082008921f7ffeed 0x6104011243efffdd 0x180000000ffffffc 0x0300000001ffffff

def z1132 : W := mkw 0x1598174002980186 0x02b302e800530030 0x57f807f003980180 0xcaff00fe00730030

def z1133 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0xbf07fe0f8f87ffff 0x77e0ffc1f1f0ffff

def z1134 : W := mkw 0x15b81fd01ef82fae 0x22b703fa03df05f5 0xd7f81ff00ff807fe 0xfaff03fe01ff00ff

def z1135 : W := mkw 0x27dff76de008088c 0x24fbfeedbc010111 0xfffffffff078f99f 0xfffffffffe0f1f33

def z1136 : W := mkw 0x086288b65ce36771 0xc10c5116cb9c6cee 0xe8e699fe7c6767ff 0xbd1cd33fcf8cecff

def z1137 : W := mkw 0x26f7c02d4b56d000 0x04def805a96ada00 0xdfffe00e0ffff805 0xfbfffc01c1ffff00

def z1138 : W := mkw 0x006288264c434441 0x000c5104c9886888 0xe8e699fe7c676667 0xbd1cd33fcf8ceccc

def z1139 : W := mkw 0x01001c0b04810551 0x80200381609020aa 0xb819fe0f8078ffff 0xd7033fc1f00f1fff

def z1140 : W := mkw 0x0eb548921f77f661 0x41d6a91243eefecc 0x1f1960000ffffe64 0x43e32c0001ffffcc

def z1141 : W := mkw 0x0042802440000000 0x0008500488000000 0xe8e699fe70606007 0xbd1cd33fce0c0c00

def z1142 : W := mkw 0x15b83fd0aef80786 0x02b707fa15df00f0 0xf7f81ff1fff80786 0xfeff03fe3fff00f0

def z1143 : W := mkw 0x0042802440000000 0x0008500488000000 0xe8e699fe70000667 0xbd1cd33fce0000cc

def z1144 : W := mkw 0x09083fbff4a92ffd 0xe12107f7fe9525ff 0x20001ffff00007fa 0x040003fffe0000ff

def z1145 : W := mkw 0x15b81fd01ef827a6 0x02b703fa03df04f4 0xd7f89ff07ff86786 0xfaff13fe0fff0cf0

def z1146 : W := mkw 0x06f7c0244b56d000 0x00def804896ada00 0xffffe00e7ffff805 0xfffffc01cfffff00

def z1147 : W := mkw 0x24fae3e4fa7a7aac 0x249f5c7c9f4f4f55 0x40f8e1f070787800 0x881f1c3e0e0f0f00

def z1148 : W := mkw 0x082008921c636661 0x41040112438c6ccc 0x880600000c676665 0x3100c000018ceccc

def z1149 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0xbf1f7e0f8f9f9fff 0x77e3efc1f1f3f3ff

def z1150 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0xd7fee0000fff7804 0xfaffdc0001ffef00

def z1151 : W := mkw 0x084280a650236261 0x41085014ca046c4c 0xe8e699fe70676667 0xbd1cd33fce0ceccc

def z1152 : W := mkw 0x15b81fd20ef907c7 0x02b703fa41df20f8 0xf7f81ffe0ff807e6 0xfeff03ffc1ff00fc

def z1153 : W := mkw 0x27d7d46d40000000 0x04fafa8da8000000 0x47e699fe70000000 0xa8fcd33fce000000

def z1154 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xd7f97ff00ff89f86 0xfaff2ffe01ff13f0

def z1155 : W := mkw 0x186288b65ceb67e7 0x430c5116cb9d6cfc 0xe8e699fe7c6767e7 0xbd1cd33fcf8cecfc

def z1156 : W := mkw 0x2247c02d40000000 0x0448f805a8000000 0xe0e699fe70000003 0xbc1cd33fce000000

def z1157 : W := mkw 0x1db81fd21efb67e7 0x43b703fa43df6cfc 0xfffe1ffe0fff67e7 0xffffc3ffc1ffecfc

def z1158 : W := mkw 0x086288b65c6b6eed 0x610c5116cb8d6ddd 0xf8fff9fe7c7fffff 0xff1fff3fcf8fffff

def z1159 : W := mkw 0x00082380b0282aac 0x2001047016050555 0x1819e781f078fffc 0xc3033cf03e0f1fff

def z1160 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0xdfffe6018ffff99d 0xfbfffcc031ffff33

def z1161 : W := mkw 0x15b83fd0aef80786 0x02b707fa15df00f0 0xd7f8fff07ff80786 0xfaff1ffe0fff00f0

def z1162 : W := mkw 0x04b008100e500400 0x0096010201ca0080 0x47e018700f800000 0x28fc030e01f00000

def z1163 : W := mkw 0x06d7c02443149000 0x00daf80488629200 0xf7fff9fe73989803 0xfeffff3fce731300

def z1164 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0x4fffe0000ffff801 0xa9fffc0001ffff00

def z1165 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xeffffffff000f803 0xfdfffffffe001f00

def z1166 : W := mkw 0x05b817c00a780284 0x00b702f8014f0050 0xd7f81ff00ff80786 0xfaff03fe01ff00f0

def z1167 : W := mkw 0x1db01cd21ef36763 0x43b6039a43de6cec 0x4fe018700fe76664 0x29fc030e01fceccc

def z1168 : W := mkw 0x0a47c0265107f061 0x4148f804ca20fe0c 0x2806800e70076061 0x0500d001ce00ec0c

def z1169 : W := mkw 0x182008921ef36763 0x4304011243de6cec 0x080000000fe76664 0x0100000001fceccc

def z1170 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0x40e619fe7c070000 0x281cc33fcf80e000

def z1171 : W := mkw 0x15b83fd0bef82fae 0x22b707fa17df05f5 0xf7f8fff1fff87ffe 0xfeff1ffe3fff0fff

def z1172 : W := mkw 0x26d7e02de0000000 0x04dafc05bc000000 0xe7fff9fff0000003 0xfcffff3ffe000000

def z1173 : W := mkw 0x15b817d00af80386 0x02b702fa015f0070 0x47f801f003f80000 0x88ff003e007f0000

def z1174 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0xa7071e0f8f8707fb 0x74e0e3c1f1f0e0ff

def z1175 : W := mkw 0x0a47c0245106f020 0x4148f8048a20de04 0x0807e0007007f801 0x0100fc000e00ff00

def z1176 : W := mkw 0x16f7c0500b56d002 0x02def80a016ada00 0xdfffe0700ffff805 0xfbfffc0e01ffff00

def z1177 : W := mkw 0x006288b44c624600 0x000c5116898c48c0 0xe8e699fe7c676607 0xbd1cd33fcf8cecc0

def z1178 : W := mkw 0x21083feff4a92ffd 0xa42107fdfe9525ff 0x20001ffff00007fa 0x040003fffe0000ff

def z1179 : W := mkw 0x082008921c6b6eed 0x61040112438d6ddd 0x080000000c7f7e64 0x01000000018fefcc

def z1180 : W := mkw 0x2247e02df106f828 0x2448fc05be20df05 0x2807e00ff007f879 0x0500fc01fe00ff0f

def z1181 : W := mkw 0x082008921c636661 0x41040112438c6ccc 0xb80106018c67e7ff 0x570020c0318cfcff

def z1182 : W := mkw 0x27dff76de1048000 0x04fbfeedbc209000 0xf7fffffff3808003 0xfefffffffe701000

def z1183 : W := mkw 0x0a47c02f5107f071 0xc148f805ea20fe0e 0x2807e00ff007f879 0x0500fc01fe00ff0f

def z1184 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xeffffffffc070007 0xfdffffffff80e000

def z1185 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xeffffffff000807b 0xfdfffffffe00100f

def z1186 : W := mkw 0x27dff76de1048000 0x04fbfeedbc209000 0xfffffffffffff807 0xffffffffffffff00

def z1187 : W := mkw 0x15b85fd00ef81786 0x02b70bfa01df02f0 0xd7f87ff00ff81f86 0xfaff0ffe01ff03f0

def z1188 : W := mkw 0x06b540000b56d000 0x00d6a800016ada00 0x9f1f60000ffff805 0x73e3ec0001ffff00

def z1189 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xdffe1ff00fff0787 0xfbffc3fe01ffe0f0

def z1190 : W := mkw 0x15b81fd01ef827a6 0x02b703fa03df04f4 0xfff9fff07ff8ffe7 0xffff3ffe0fff1ffc

def z1191 : W := mkw 0x0042802640010041 0x00085004c8002008 0xe8e699fe70070063 0xbd1cd33fce00e00c

def z1192 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0x60e699fe7c676662 0xac1cd33fcf8ceccc

def z1193 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0x68e619fe7c676666 0x2d1cc33fcf8ceccc

def z1194 : W := mkw 0x15b83fd0aef80f8e 0x22b707fa15df01f1 0xd7f81ff18ff8079e 0xfaff03fe31ff00f3

def z1195 : W := mkw 0x15b01cd01ef82fae 0x22b6039a03df05f5 0x5fe018700ff8fffc 0x2bfc030e01ff1fff

def z1196 : W := mkw 0x102008921ffdafff 0xa204011243ffb5ff 0x180000000ffffffc 0x0300000001ffffff

def z1197 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xe7e69ffff0000003 0xbcfcd3fffe000000

def z1198 : W := mkw 0x224fe32de106d000 0x0449fc65bc20da00 0xb81fe78ff07ff807 0xd703fcf1fe0fff00

def z1199 : W := mkw 0x05b83740aa500000 0x00b706e8154a0000 0xfff9fff1fff8f807 0xffff3ffe3fff1f00

def z1200 : W := mkw 0x082008b65c612661 0x41040116cb8c24cc 0xe8e619fe7c670667 0xbd1cc33fcf8ce0cc

def z1201 : W := mkw 0x086288364c434441 0x410c5106c9886888 0x40e699fe7c070000 0xa81cd33fcf80e000

def z1202 : W := mkw 0x15b81fdb0ef907d7 0x82b703fb61df20fa 0xfffe1fff8fff07ff 0xffffc3fff1ffe0ff

def z1203 : W := mkw 0x11083fdbb4a92fff 0xa22107fb769525ff 0x20001ffff00007fa 0x040003fffe0000ff

def z1204 : W := mkw 0x084288b654236661 0x41085116ca846ccc 0xe8e699fe70076663 0xbd1cd33fce00eccc

def z1205 : W := mkw 0x0042802440000000 0x0008500488000000 0xf8fff9fe7078f807 0xff1fff3fce0f1f00

def z1206 : W := mkw 0x15b014500ad00102 0x02b6028a015a0020 0x47e0007003800000 0x08fc000e00700000

def z1207 : W := mkw 0x27dff76de3949110 0x84fbfeedbc729222 0xf7fffffff398999b 0xfefffffffe731333

def z1208 : W := mkw 0x086280b458626220 0x410c50168b0c4c44 0xe8e699fe7c676007 0xbd1cd33fcf8cec00

def z1209 : W := mkw 0x26dfe36de0000000 0x04dbfc6dbc000000 0xe0fff9fff0000003 0xbc1fff3ffe000000

def z1210 : W := mkw 0x06b540000b56d000 0x00d6a800016ada00 0xdff960000ffff804 0xfbff2c0001ffff00

def z1211 : W := mkw 0x0a4fe3a6f12ffaed 0x6149fc74de25ff5d 0xb81fe78ff07fffff 0xd703fcf1fe0fffff

def z1212 : W := mkw 0x27dff76de1848110 0x84fbfeedbc309022 0xfffffffff38087ff 0xfffffffffe7010ff

def z1213 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0x67f9fffff0000002 0xccff3ffffe000000

def z1214 : W := mkw 0x15b81fd90ef80786 0x02b703fb21df00f0 0xf7f81fff8ff80786 0xfeff03fff1ff00f0

def z1215 : W := mkw 0x2247e02de1048010 0x8448fc05bc209002 0x2007e00ff0008019 0x0400fc01fe001003

def z1216 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xe7fef9fe70000003 0xbcffdf3fce000000

def z1217 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xe7fffffff00007fb 0xfcfffffffe0000ff

def z1218 : W := mkw 0x086288b65c636e69 0x610c5116cb8c6dcd 0xe8e699fe7c67fe7f 0xbd1cd33fcf8cffcf

def z1219 : W := mkw 0x15b81f500ed80586 0x02b703ea01db00b0 0xd7f81ff00f980182 0xfaff03fe01f30030

def z1220 : W := mkw 0x00082380b0282aac 0x2001047016050555 0x3019e781f078fffa 0xc6033cf03e0f1fff

def z1221 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xdff91ff00ff88787 0xfbff23fe01ff10f0

def z1222 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0x67fefffff0000002 0xacffdffffe000000

def z1223 : W := mkw 0x0247802440000000 0x0048f00488000000 0xe7e799fe70000003 0xfcfcf33fce000000

def z1224 : W := mkw 0x15b81fd01ef82fae 0x22b703fa03df05f5 0xfff91ff18ff8ffff 0xffff23fe31ff1fff

def z1225 : W := mkw 0x07dfd76440000000 0x00fbfaec88000000 0xe7fffffe70000003 0xfcffffffce000000

def z1226 : W := mkw 0x05901c4004800500 0x00b20388009000a0 0xd7e01e700f800786 0x7afc03ce01f000f0

def z1227 : W := mkw 0x0a47c0264107d041 0x4148f804c820fa08 0x0807e00e0007f801 0x0100fc01c000ff00

def z1228 : W := mkw 0x04da836440000000 0x009b506c88000000 0xe0fe99fe70000003 0xbc1fd33fce000000

def z1229 : W := mkw 0x086288b65c6b6eed 0x610c5116cb8d6ddd 0xe8e699fe7c6767ff 0xbd1cd33fcf8cecff

def z1230 : W := mkw 0x0247802d40000000 0x0048f005a8000000 0xe0e799fff0000003 0xbc1cf33ffe000000

def z1231 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xc7fff9fe70000001 0xf8ffff3fce000000

def z1232 : W := mkw 0x15b83fd0bef82fae 0x22b707fa17df05f5 0xfff89ff1fff867ff 0xffff13fe3fff0cff

def z1233 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xc7f819f00ff80606 0xb8ff033e01ff00c0

def z1234 : W := mkw 0x0a4780af5127e271 0xc148f015ea24fc4e 0xb807878ff067e7ff 0xd700f0f1fe0cfcff

def z1235 : W := mkw 0x0000002440000000 0x0000000488000000 0xe0e019fe70000002 0xbc1c033fce000000

def z1236 : W := mkw 0x0ef7c0344b56d000 0x41def806896ada00 0xdfffe0700ffff805 0xfbfffc0e01ffff00

def z1237 : W := mkw 0x15b81f500ed00502 0x02b703ea01da00a0 0xd7f81ff00f800786 0xfaff03fe01f000f0

def z1238 : W := mkw 0x15b81f500ed80586 0x02b703ea01db00b0 0x47f818700f980000 0x28ff030e01f30000

def z1239 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0x47fffffff0000000 0xe8fffffffe000000

def z1240 : W := mkw 0x15b83fd0aef80f8e 0x22b707fa15df01f1 0xfff97ff18ff89fff 0xffff2ffe31ff13ff

def z1241 : W := mkw 0x15b01c500ed00502 0x02b6038a01da00a0 0xc7e018700fe00004 0xb8fc030e01fc0000

def z1242 : W := mkw 0x182008921ffff7e7 0x4304011243fffefc 0x180000000fffffe4 0x0300000001fffffc

def z1243 : W := mkw 0x15b81fd01ef82fae 0x22b703fa03df05f5 0xdff9fff00ff8ffff 0xfbff3ffe01ff1fff

def z1244 : W := mkw 0x2a47e02ff107e071 0xc548fc05fe20fc0e 0x2807e00ff007e079 0x0500fc01fe00fc0f

def z1245 : W := mkw 0x15b83fd0aef80786 0x02b707fa15df00f0 0xfff9fff1fff8ff87 0xffff3ffe3fff1ff0

def z1246 : W := mkw 0x15b01c500ed00502 0x02b6038a01da00a0 0xd7f81e700ff80786 0xfaff03ce01ff00f0

def z1247 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0xbf1ffe0f8f8787ff 0xf7e3ffc1f1f0f0ff

def z1248 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0xbf071e0f8fffffff 0x77e0e3c1f1ffffff

def z1249 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0x47f81ff00ff80782 0xa8ff03fe01ff00f0

def z1250 : W := mkw 0x0a67c8921d67f661 0x414cf91243acfecc 0x0807e0000c67fe65 0x0100fc00018cffcc

def z1251 : W := mkw 0x0b251c9b1de7e771 0xc164a39363bcfcee 0x1f0106018fe7e7fc 0x43e020c031fcfcff

def z1252 : W := mkw 0x100823d0b0282aae 0x2201047a16050555 0xb819e7f1f078ffff 0xd7033cfe3e0f1fff

def z1253 : W := mkw 0x27dff76de316d000 0x04fbfeedbc62da00 0xfffffffff39ff803 0xfffffffffe73ff00

def z1254 : W := mkw 0x2247e02de106d000 0x0448fc05bc20da00 0x2007e00ff0070001 0x0400fc01fe00e000

def z1255 : W := mkw 0x15b81fd01ef82fae 0x22b703fa03df05f5 0xfff89ff07ff8ffff 0xffff13fe0fff1fff

def z1256 : W := mkw 0x15b83fd0bef82fae 0x22b707fa17df05f5 0xd7f81ff07ff80786 0xfaff03fe0fff00f0

def z1257 : W := mkw 0x082008921d67e661 0x4104011243acfccc 0x180000000fe7e664 0x0300000001fcfccc

def z1258 : W := mkw 0x15b01c500ed00502 0x02b6038a01da00a0 0x57e018700ff80004 0x2afc030e01ff0000

def z1259 : W := mkw 0x15da976442980186 0x02bb52ec88530030 0xf7fe9ffe73980183 0xfeffd3ffce730030

def z1260 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xdff81ff00ff8ff86 0xfbff03fe01ff1ff0

def z1261 : W := mkw 0x27dff76de1848110 0x84fbfeedbc309022 0xffffffffff87819f 0xfffffffffff0f033

def z1262 : W := mkw 0x01201c100cc00500 0x00240382019800a0 0x47e018700f800000 0x28fc030e01f00000

def z1263 : W := mkw 0x082008921e736661 0x4104011243ce6ccc 0x180000000fff6664 0x0300000001ffeccc

def z1264 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xd7e01ff00f800786 0x7afc03fe01f000f0

def z1265 : W := mkw 0x2247c02d4106d000 0x0448f805a820da00 0x0006000e00070000 0x0000c001c000e000

def z1266 : W := mkw 0x15b01c500ed00502 0x02b6038a01da00a0 0xc7e018700f800606 0x38fc030e01f000c0

def z1267 : W := mkw 0x06f7c0000b56d000 0x00def800016ada00 0x57ffe0000ffff800 0xeafffc0001ffff00

def z1268 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0x68e699fe7c076663 0x2d1cd33fcf80eccc

def z1269 : W := mkw 0x05b014400a500000 0x00b60288014a0000 0x47e018700f800000 0x28fc030e01f00000

def z1270 : W := mkw 0x15b81fd20ef907c7 0x02b703fa41df20f8 0xffff1fff8fff87ff 0xffffe3fff1fff0ff

def z1271 : W := mkw 0x05981fc004a80784 0x00b303f8009500f0 0xd7f81ff00ff80786 0xfaff03fe01ff00f0

def z1272 : W := mkw 0x15b01cd00ef80786 0x02b6039a01df00f0 0xd7f818700ff80784 0xfaff030e01ff00f0

def z1273 : W := mkw 0x0247802441048000 0x0048f00488209000 0xffe799fe7f878007 0xfffcf33fcff0f000

def z1274 : W := mkw 0x006288b64c610641 0x000c5116c98c20c8 0xe8e699fe7c670667 0xbd1cd33fcf8ce0cc

def z1275 : W := mkw 0x15b81fd00ef80f8e 0x22b703fa01df01f1 0xd7f81ff00ff89f9e 0xfaff03fe01ff13f3

def z1276 : W := mkw 0x0000008010202220 0x0000001002040444 0xb819e781f078ffff 0xd7033cf03e0f1fff

def z1277 : W := mkw 0x15b81fd20ef907d7 0x82b703fa41df20fa 0xd7f81ff00ff807fe 0xfaff03fe01ff00ff

def z1278 : W := mkw 0x15b01cd00ef80786 0x02b6039a01df00f0 0xd7e01e700ff80786 0x7afc03ce01ff00f0

def z1279 : W := mkw 0x00082380b0282aac 0x2001047016050555 0x2819e781f078fffb 0x85033cf03e0f1fff

def z1280 : W := mkw 0x26dfe364e0000000 0x04dbfc6c9c000000 0xe7fff9fe70000003 0xfcffff3fce000000

def z1281 : W := mkw 0x15b837d0baf82bae 0x22b706fa175f0575 0xfff9e7f1f3f8ffff 0xdfff3cfe3e7f1fff

def z1282 : W := mkw 0x004aa324e0000000 0x000954649c000000 0xe0e69ffff0000003 0xbc1cd3fffe000000

def z1283 : W := mkw 0x14b803d00a780286 0x0297007a014f0050 0x47f801f00ff80000 0xa8ff003e01ff0000

def z1284 : W := mkw 0x15b01c500ed00502 0x02b6038a01da00a0 0x47e01e700f800782 0x28fc03ce01f000f0

def z1285 : W := mkw 0x224fe3adf12efaac 0x2449fc75be25df55 0xb81fe78ff07fffff 0xd703fcf1fe0fffff

def z1286 : W := mkw 0x15b81fd00ef00702 0x02b703fa01de00e0 0xc7f81ff00fe00606 0xf8ff03fe01fc00c0

def z1287 : W := mkw 0x01201c900ce00700 0x00240392019c00e0 0xc7e019f00fe00606 0xb8fc033e01fc00c0

def z1288 : W := mkw 0x27dff76de008088c 0x24fbfeedbc010111 0xe7fffffff0181803 0xfcfffffffe030300

def z1289 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xf7ffffffff800007 0xfefffffffff00000

def z1290 : W := mkw 0x15b81f500ed00502 0x02b703ea01da00a0 0x47f81e700f800000 0x68ff03ce01f00000

def z1291 : W := mkw 0x06d7c00001048000 0x00daf80000209000 0xdfffe0000ffff805 0xfbfffc0001ffff00

def z1292 : W := mkw 0x15b81fdb0ef907d7 0x82b703fb61df20fa 0xfff91fff8ff887ff 0xffff23fff1ff10ff

def z1293 : W := mkw 0x379d7749a39c8196 0x86f3aee934739032 0x1719660183988198 0x42e32cc030731033

def z1294 : W := mkw 0x086288921c636661 0x410c5112438c6ccc 0x080680000c676665 0x0100d000018ceccc

def z1295 : W := mkw 0x15b83fd0aef80f8e 0x22b707fa15df01f1 0xdff9fff18ff8ff9f 0xfbff3ffe31ff1ff3

def z1296 : W := mkw 0x0247c02440000000 0x0048f80488000000 0xe0e7f9fe70000003 0xbc1cff3fce000000

def z1297 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xd7f8fff00ff87f86 0xfaff1ffe01ff0ff0

def z1298 : W := mkw 0x00082300a0000000 0x0001046014000000 0xb819e781f078ffff 0xd7033cf03e0f1fff

def z1299 : W := mkw 0x27dff76de0000000 0x04fbfeedbc000000 0xe7fffffff0787803 0xfcfffffffe0f0f00

def z1300 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xe0e619fe7c670666 0xbc1cc33fcf8ce0cc

def z1301 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xf7f91ff18ff80787 0xfeff23fe31ff00f0

def z1302 : W := mkw 0x0ff7dc3f4fd7d551 0xc1fefb87e9fafaaa 0x47e6187e0f870000 0x28fcc30fc1f0e000

def z1303 : W := mkw 0x2247e024e106d000 0x0448fc049c20da00 0x0807e0007007f801 0x0100fc000e00ff00

def z1304 : W := mkw 0x082008921c6b66e5 0x41040112438d6cdc 0x180000000c7f67e4 0x03000000018fecfc

def z1305 : W := mkw 0x25dab76de0000000 0x04bb56edbc000000 0xe7fe9ffff0000003 0xfcffd3fffe000000

def z1306 : W := mkw 0x15b81fd00ef80786 0x02b703fa01df00f0 0xfff81ff00ff807e7 0xffff03fe01ff00fc

def z1307 : W := mkw 0x03051c0b05858551 0x8060a38160b0b0aa 0xb7061e0f8f8707fe 0x76e0c3c1f1f0e0ff

def z1308 : W := mkw 0x2598376de0000000 0x04b306edbc000000 0x60f81ffff0000002 0x8c1f03fffe000000

def z1309 : W := mkw 0x086288b65c636661 0x410c5116cb8c6ccc 0xe8fef9fe7c7f7e67 0xbd1fdf3fcf8fefcc

def z1310 : W := mkw 0x234fb76de0000000 0x0469f6edbc000000 0xe7e79ffff0000003 0xfcfcf3fffe000000

def z1311 : W := mkw 0x06f7c0090b56d000 0x00def801216ada00 0xffffe00f8ffff805 0xfffffc01f1ffff00

def z1312 : W := mkw 0x2247c02f41058051 0x8448f805e820b00a 0x2807000f80078079 0x0500e001f000f00f

def z1313 : W := mkw 0x0598176440000000 0x00b302ec88000000 0xe7f81ffe70000002 0xfcff03ffce000000

def z1314 : W := mkw 0x27dff76de0080084 0x04fbfeedbc010010 0xf7fffffff0180183 0xfefffffffe030030

def z1315 : W := mkw 0x27dff76de3149000 0x04fbfeedbc629200 0xe7fffffff3800003 0xfcfffffffe700000

def z1316 : W := mkw 0x15b817500ad80186 0x02b702ea015b0030 0x57f8067003980180 0x4aff00ce00730030

def z1317 : W := mkw 0x35b87fd0aef80786 0x06b70ffa15df00f0 0xd7f87ff00ff80786 0xfaff0ffe01ff00f0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z8,z9,z6]),(0,[z7,z10,z2,z3,z4,z5,z6]),(0,[z11,z7,z2,z3,z12,z4,z5])],[(0,[z7,z2,z3,z4,z13,z9,z6]),(0,[z7,z2,z3,z4,z9,z14,z6]),(0,[z15,z7,z2,z3,z4,z5,z6]),(0,[z16,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z17,z6]),(0,[z7,z18,z2,z19,z3,z4,z6]),(0,[z7,z2,z4,z20,z5,z21,z6])],[(1,[z7,z22,z2,z4,z5,z6]),(0,[z7,z2,z3,z23,z4,z5,z6]),(0,[z7,z2,z3,z4,z9,z6,z24]),(1,[z7,z2,z3,z4,z5,z25]),(0,[z7,z2,z3,z5,z26,z6,z27]),(0,[z7,z2,z3,z4,z28,z5,z6])],[(0,[z0,z7,z2,z3,z4,z29,z6]),(0,[z30,z7,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z20,z9,z6]),(0,[z7,z2,z31,z3,z12,z4,z5]),(1,[z7,z2,z3,z4,z5,z32])],[(0,[z7,z33,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z34,z6]),(0,[z7,z2,z35,z3,z4,z5,z6]),(0,[z36,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z37,z9,z6]),(0,[z7,z2,z38,z3,z4,z29,z6]),(0,[z7,z39,z2,z3,z4,z5,z6]),(0,[z40,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z5,z41,z6,z24])],[(0,[z7,z2,z3,z4,z5,z42,z6]),(0,[z7,z43,z2,z3,z4,z5,z14])],[(0,[z7,z44,z2,z3,z4,z5,z6]),(0,[z45,z2,z3,z4,z29,z5,z6]),(0,[z7,z2,z46,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z47,z5,z6]),(0,[z7,z2,z3,z4,z5,z48,z6]),(0,[z7,z43,z2,z49,z3,z4,z5])]],
   [[(1,[z7,z2,z3,z4,z29,z6]),(0,[z7,z50,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z51,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z52,z6])],[(0,[z7,z2,z53,z3,z4,z5,z6]),(0,[z54,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z12,z4,z55,z5]),(0,[z7,z2,z3,z56,z4,z5,z6])],[(0,[z57,z7,z2,z3,z4,z5,z6]),(0,[z58,z7,z2,z3,z12,z4,z5]),(0,[z7,z2,z3,z12,z4,z9,z6]),(0,[z7,z2,z3,z4,z29,z59,z6]),(0,[z7,z2,z3,z4,z5,z60,z27]),(0,[z7,z61,z2,z3,z12,z4,z5]),(0,[z7,z2,z3,z4,z5,z62,z6]),(0,[z7,z63,z2,z64,z4,z5,z6]),(0,[z7,z63,z2,z3,z4,z5,z65])],[(0,[z7,z2,z3,z4,z9,z66,z6]),(0,[z7,z67,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z68]),(0,[z7,z2,z3,z4,z5,z6,z69]),(0,[z7,z2,z64,z3,z4,z5,z70]),(0,[z7,z63,z2,z4,z5,z70,z6])],[(0,[z7,z2,z3,z4,z71,z5,z6]),(0,[z7,z2,z3,z4,z5,z72,z6]),(0,[z7,z2,z3,z4,z5,z6,z73]),(0,[z7,z2,z3,z4,z5,z74,z6]),(0,[z7,z2,z3,z75,z4,z5,z6])],[(0,[z7,z2,z3,z76,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z77,z6])],[(0,[z7,z7,z2,z3,z4,z5,z6]),(0,[z78,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z79,z3,z4,z29,z6]),(0,[z7,z2,z3,z4,z80,z5,z6]),(0,[z7,z81,z2,z3,z4,z5,z6]),(0,[z7,z2,z82,z3,z4,z5,z6])],[(0,[z0,z2,z83,z3,z4,z5,z6]),(0,[z84,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z85,z5,z6]),(0,[z86,z7,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z87,z4,z5,z6]),(1,[z7,z2,z88,z4,z5,z6]),(0,[z7,z2,z3,z89,z4,z5,z6]),(0,[z90,z7,z2,z3,z4,z5,z6]),(0,[z7,z91,z2,z3,z4,z29,z6]),(0,[z7,z2,z3,z4,z92,z29,z6]),(1,[z7,z93,z2,z13,z5,z6]),(0,[z7,z18,z2,z3,z12,z4,z5]),(0,[z7,z2,z94,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z95,z5,z6]),(0,[z7,z2,z3,z96,z4,z5,z6]),(1,[z7,z63,z2,z4,z5,z70]),(0,[z7,z43,z2,z3,z97,z4,z5])],[(0,[z98,z7,z43,z2,z3,z4,z5]),(0,[z7,z2,z3,z99,z4,z5,z6]),(1,[z7,z43,z2,z3,z5,z24]),(0,[z7,z2,z3,z4,z100,z5,z6])],[(0,[z7,z2,z3,z101,z4,z5,z6]),(0,[z7,z2,z3,z4,z102,z29,z6]),(0,[z7,z103,z2,z3,z4,z5,z6])],[(0,[z7,z22,z2,z83,z4,z5,z6]),(0,[z104,z7,z2,z3,z4,z5,z6]),(0,[z7,z43,z2,z3,z105,z4,z5]),(0,[z7,z2,z49,z3,z4,z9,z6]),(0,[z7,z2,z3,z106,z4,z5,z6]),(0,[z107,z7,z43,z2,z3,z4,z5]),(0,[z7,z108,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z12,z4,z109])],[(0,[z7,z2,z3,z110,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z111,z6]),(0,[z7,z2,z112,z3,z4,z5,z6]),(0,[z113,z7,z2,z3,z12,z4,z5])],[(0,[z7,z2,z3,z4,z29,z6,z114]),(0,[z7,z67,z2,z51,z4,z5,z6]),(1,[z7,z2,z3,z4,z115,z6]),(0,[z7,z2,z3,z4,z5,z6,z116]),(0,[z7,z43,z2,z3,z4,z5,z41]),(0,[z7,z2,z49,z3,z4,z102,z6])],[(0,[z0,z7,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z9,z70,z6]),(0,[z7,z3,z4,z55,z5,z117,z6])]],
   [[(1,[z7,z2,z3,z4,z118,z6]),(0,[z7,z2,z3,z119,z4,z5,z6]),(0,[z7,z2,z120,z3,z4,z5,z6]),(0,[z121,z7,z2,z3,z4,z29,z6]),(0,[z7,z2,z122,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z123,z5,z6]),(0,[z7,z43,z2,z3,z4,z5,z21])],[(0,[z124,z7,z2,z3,z4,z5,z6]),(1,[z7,z125,z2,z3,z5,z6]),(0,[z7,z2,z3,z4,z126,z5,z6]),(0,[z7,z43,z2,z19,z3,z4,z5]),(0,[z7,z43,z2,z3,z4,z5,z70]),(0,[z7,z2,z3,z4,z5,z127,z6]),(0,[z7,z43,z2,z3,z4,z5,z114])],[(0,[z7,z2,z3,z4,z128,z5,z6]),(0,[z30,z7,z43,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z129,z6]),(0,[z130,z7,z2,z3,z4,z5,z6]),(0,[z7,z131,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z132,z4,z5,z6])],[(0,[z7,z133,z2,z3,z4,z20,z6]),(0,[z7,z2,z3,z12,z5,z41,z6])],[(0,[z7,z2,z3,z4,z5,z6,z134]),(1,[z7,z2,z3,z4,z5,z135])],[(0,[z7,z136,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z137]),(0,[z138,z7,z2,z3,z4,z5,z6])],[(0,[z98,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z139,z3,z4,z5,z6]),(0,[z58,z7,z2,z3,z4,z29,z6]),(0,[z7,z2,z3,z4,z9,z140,z6]),(0,[z7,z61,z2,z3,z4,z29,z6]),(0,[z7,z2,z3,z4,z5,z73,z27]),(0,[z7,z141,z2,z3,z4,z5,z6]),(0,[z7,z142,z2,z3,z4,z55,z6]),(0,[z143,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z144,z4,z5])],[(0,[z7,z145,z2,z3,z4,z5,z6]),(0,[z146,z30,z2,z3,z4,z5,z6]),(0,[z147,z7,z2,z3,z4,z29,z6]),(0,[z7,z2,z3,z96,z37,z5,z6]),(0,[z7,z2,z3,z4,z5,z148,z6]),(0,[z7,z149,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z150,z4,z5,z6]),(0,[z7,z93,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z151]),(1,[z7,z2,z152,z3,z4,z6]),(0,[z153,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z154,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z29,z21,z6]),(0,[z107,z7,z2,z3,z4,z5,z6]),(1,[z7,z43,z2,z155,z4,z5])],[(0,[z7,z133,z2,z3,z4,z117,z6]),(0,[z7,z156,z2,z3,z4,z5,z6]),(0,[z7,z142,z2,z3,z4,z14,z6])],[(0,[z7,z2,z19,z3,z4,z29,z6]),(1,[z7,z2,z3,z4,z5,z157]),(0,[z7,z158,z2,z3,z4,z5,z6])],[(0,[z146,z7,z2,z110,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z159,z6]),(0,[z7,z2,z160,z3,z4,z5,z6]),(0,[z161,z7,z2,z3,z4,z5,z6]),(0,[z7,z162,z2,z3,z4,z5,z6])],[(0,[z7,z91,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z163,z6]),(0,[z164,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z165,z4,z5,z6]),(1,[z7,z43,z2,z79,z3,z5]),(0,[z7,z2,z3,z12,z4,z5,z14])],[(1,[z7,z2,z3,z4,z5,z166]),(1,[z7,z167,z51,z4,z5,z6]),(0,[z7,z43,z91,z2,z3,z4,z5]),(0,[z7,z2,z4,z5,z70,z6,z65]),(0,[z7,z2,z168,z3,z4,z5,z6])],[(0,[z7,z43,z33,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z9,z117,z6]),(0,[z7,z2,z169,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z102,z9,z6]),(0,[z7,z2,z3,z4,z170,z5,z6]),(0,[z7,z2,z3,z4,z5,z27,z65]),(0,[z7,z2,z3,z4,z5,z6,z171]),(0,[z7,z63,z2,z3,z4,z5,z70]),(0,[z7,z2,z3,z12,z4,z172,z5])]],
   [[(0,[z146,z7,z2,z173,z4,z5,z6]),(0,[z7,z2,z79,z3,z4,z5,z157])],[(0,[z16,z7,z2,z3,z4,z52,z6]),(0,[z7,z2,z3,z4,z174,z5,z6]),(0,[z7,z93,z2,z3,z13,z5,z6]),(0,[z7,z175,z43,z2,z3,z4,z5]),(0,[z7,z2,z176,z3,z12,z4,z5]),(0,[z177,z7,z2,z3,z4,z5,z6])],[(0,[z7,z67,z83,z3,z4,z5,z6]),(0,[z7,z2,z178,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z179,z5,z6]),(0,[z7,z50,z2,z3,z4,z5,z6]),(0,[z7,z167,z2,z3,z12,z4,z5])],[(1,[z7,z2,z3,z180,z5,z6]),(0,[z181,z7,z2,z3,z4,z5,z6]),(0,[z7,z43,z2,z173,z3,z4,z5]),(0,[z98,z7,z2,z3,z37,z5,z6]),(0,[z7,z2,z3,z105,z4,z29,z6]),(0,[z121,z7,z2,z3,z4,z9,z6]),(1,[z7,z2,z3,z4,z182,z6]),(0,[z7,z142,z2,z3,z4,z5,z6]),(0,[z7,z18,z142,z2,z3,z4,z6]),(0,[z7,z2,z183,z3,z4,z5,z6])],[(0,[z184,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z185,z4,z5,z6]),(0,[z7,z186,z2,z3,z4,z37,z5]),(0,[z7,z61,z142,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z187])],[(0,[z0,z7,z43,z2,z3,z4,z5]),(0,[z1,z7,z43,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z29,z14,z6])],[(0,[z7,z188,z2,z3,z4,z5,z6]),(0,[z7,z43,z2,z3,z4,z9,z6]),(0,[z189,z7,z2,z3,z4,z29,z6]),(0,[z7,z2,z3,z4,z29,z6,z24]),(0,[z7,z190,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z191,z6]),(0,[z7,z2,z3,z4,z5,z192,z6])]],
   [[(0,[z193,z7,z2,z3,z4,z5,z6]),(0,[z16,z7,z2,z3,z12,z4,z5]),(0,[z7,z2,z3,z4,z5,z6,z194]),(0,[z7,z2,z3,z195,z4,z66,z6])],[(0,[z196,z7,z2,z3,z4,z5,z6]),(0,[z197,z7,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z198,z5,z6]),(0,[z7,z67,z2,z3,z4,z123,z6]),(0,[z7,z2,z3,z4,z5,z199,z6]),(0,[z7,z2,z3,z195,z4,z5,z6]),(0,[z7,z200,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z201,z5,z6]),(1,[z7,z2,z3,z12,z5,z41]),(0,[z7,z2,z3,z202,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z203])],[(0,[z7,z2,z3,z12,z105,z4,z5]),(0,[z7,z2,z204,z3,z4,z5,z6]),(0,[z7,z205,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z195,z206,z6]),(0,[z7,z43,z2,z3,z4,z5,z24])],[(0,[z147,z7,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z6,z25]),(0,[z7,z2,z3,z4,z5,z6,z207])],[(0,[z7,z208,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z209,z5,z6]),(0,[z7,z2,z3,z4,z9,z41,z6]),(1,[z107,z2,z3,z4,z5,z60]),(0,[z7,z2,z3,z4,z210,z5,z6]),(0,[z7,z43,z10,z2,z3,z4,z5]),(0,[z7,z211,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z12,z4,z5,z41])],[(0,[z7,z175,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z212]),(1,[z7,z43,z2,z97,z4,z5])],[(1,[z7,z2,z3,z4,z213,z6]),(0,[z7,z2,z19,z3,z4,z9,z6]),(0,[z7,z133,z2,z3,z12,z4,z5]),(0,[z7,z2,z49,z3,z4,z66,z6])],[(1,[z7,z2,z3,z4,z5,z214]),(0,[z7,z2,z3,z4,z5,z9,z6]),(0,[z7,z2,z215,z3,z4,z5,z6]),(0,[z7,z2,z3,z51,z12,z4,z5]),(0,[z7,z2,z3,z4,z216,z5,z6]),(0,[z7,z2,z3,z217,z4,z5,z6]),(0,[z7,z218,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z12,z4,z5,z70]),(0,[z7,z2,z3,z12,z4,z5,z114]),(0,[z7,z2,z49,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z219,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z220,z6]),(0,[z30,z2,z173,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z29,z66,z6]),(0,[z7,z2,z3,z4,z5,z221,z6])],[(0,[z7,z2,z3,z4,z29,z5,z6]),(1,[z7,z2,z3,z222,z5,z6]),(0,[z7,z223,z2,z3,z4,z5,z6])],[(0,[z1,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z83,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z224,z6]),(0,[z7,z67,z2,z3,z12,z4,z5]),(0,[z7,z142,z2,z49,z3,z4,z6]),(1,[z7,z2,z3,z132,z5,z6])],[(0,[z7,z2,z225,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z226,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z227]),(0,[z7,z141,z2,z3,z216,z5,z6])],[(0,[z7,z2,z3,z4,z5,z228,z6]),(0,[z107,z2,z3,z4,z5,z60,z6]),(0,[z7,z2,z3,z4,z229,z5,z6])],[(0,[z7,z63,z2,z3,z4,z9,z6]),(0,[z7,z2,z230,z3,z4,z5,z6]),(0,[z231,z7,z2,z3,z4,z5,z6])],[(0,[z30,z7,z2,z110,z4,z5,z6]),(0,[z7,z2,z3,z4,z232,z5,z6]),(0,[z7,z2,z3,z4,z5,z233,z66])],[(0,[z7,z67,z33,z3,z4,z5,z6]),(0,[z7,z167,z2,z3,z4,z29,z6]),(0,[z234,z7,z2,z3,z4,z5,z6]),(1,[z7,z141,z3,z96,z5,z6]),(0,[z7,z2,z3,z235,z4,z5,z6]),(0,[z7,z2,z236,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z206,z9,z6]),(1,[z7,z2,z3,z4,z5,z237]),(0,[z7,z2,z3,z238,z4,z5,z6]),(0,[z7,z239,z2,z3,z4,z5,z6])],[(0,[z7,z2,z79,z3,z240,z5,z6]),(0,[z7,z2,z3,z4,z241,z6,z65]),(0,[z7,z2,z3,z4,z102,z5,z14])],[(0,[z146,z7,z43,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z242,z5,z6]),(0,[z7,z2,z19,z3,z195,z4,z6]),(0,[z7,z2,z3,z4,z5,z243,z6])],[(0,[z7,z2,z3,z4,z5,z244,z6]),(0,[z30,z7,z2,z173,z4,z5,z6]),(0,[z7,z2,z3,z4,z245,z5,z6]),(0,[z189,z7,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z246,z5,z6]),(0,[z7,z247,z2,z3,z4,z5,z6]),(0,[z7,z2,z248,z3,z4,z5,z6])],[(0,[z146,z7,z249,z3,z4,z5,z6]),(0,[z7,z2,z3,z110,z12,z4,z5]),(0,[z98,z7,z2,z3,z4,z5,z134]),(0,[z16,z7,z2,z3,z4,z29,z6]),(0,[z7,z2,z3,z4,z29,z70,z6]),(0,[z7,z43,z2,z3,z51,z4,z5]),(0,[z7,z43,z142,z2,z3,z4,z5]),(0,[z7,z2,z64,z3,z4,z5,z6])],[(0,[z7,z2,z3,z250,z4,z5,z6]),(0,[z7,z2,z3,z251,z4,z5,z6]),(0,[z7,z2,z3,z4,z9,z6,z27]),(0,[z7,z252,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z253,z5,z6]),(0,[z7,z2,z3,z254,z4,z5,z6]),(0,[z7,z141,z2,z3,z96,z5,z6]),(0,[z7,z93,z2,z4,z13,z5,z6]),(0,[z7,z43,z43,z2,z3,z4,z5])],[(1,[z147,z2,z3,z37,z5,z6]),(1,[z2,z3,z4,z29,z9,z6]),(0,[z7,z2,z3,z4,z5,z182,z6]),(0,[z7,z2,z3,z4,z5,z255,z6]),(0,[z7,z2,z256,z3,z4,z5,z6]),(0,[z7,z43,z2,z3,z4,z5,z66])]],
   [[(1,[z7,z2,z3,z4,z245,z6]),(0,[z197,z7,z43,z2,z3,z4,z5]),(0,[z7,z257,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z206,z5,z66,z6])],[(0,[z7,z258,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z259]),(0,[z7,z260,z2,z3,z4,z5,z6]),(0,[z7,z261,z2,z3,z4,z5,z6]),(1,[z7,z133,z2,z4,z20,z6]),(0,[z7,z2,z3,z4,z5,z262,z6]),(0,[z7,z131,z2,z3,z12,z4,z5])],[(0,[z263,z7,z2,z3,z4,z5,z6]),(0,[z7,z133,z2,z3,z4,z29,z6]),(0,[z7,z2,z3,z264,z4,z5,z6]),(0,[z7,z265,z2,z3,z4,z5,z6])],[(0,[z7,z266,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z6,z267]),(0,[z7,z2,z3,z4,z5,z268,z6]),(0,[z7,z2,z19,z3,z4,z55,z6])],[(0,[z7,z2,z3,z4,z269,z5,z6]),(0,[z7,z2,z3,z96,z105,z5,z6]),(0,[z7,z2,z3,z4,z5,z270,z6]),(0,[z271,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z272,z6])],[(0,[z0,z7,z2,z87,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z273,z6]),(0,[z98,z7,z2,z3,z12,z4,z5]),(0,[z7,z2,z3,z4,z5,z274,z6]),(0,[z275,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z276,z6]),(0,[z7,z141,z2,z3,z12,z4,z5]),(0,[z7,z2,z3,z4,z5,z6,z135]),(0,[z7,z2,z3,z277,z4,z5,z6])],[(0,[z7,z2,z3,z4,z278,z5,z6]),(0,[z7,z279,z2,z3,z4,z5,z6]),(0,[z146,z7,z2,z3,z4,z5,z6]),(0,[z45,z7,z2,z3,z12,z4,z5]),(0,[z7,z2,z3,z4,z5,z60,z65]),(0,[z7,z280,z2,z3,z4,z5,z6]),(1,[z16,z7,z3,z216,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z137]),(0,[z7,z93,z2,z3,z12,z4,z5]),(0,[z7,z2,z3,z12,z4,z281,z5])],[(0,[z282,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z173,z3,z12,z4,z5]),(0,[z107,z7,z2,z3,z12,z4,z5]),(0,[z7,z43,z93,z2,z3,z5,z6]),(0,[z7,z43,z2,z3,z240,z4,z5]),(0,[z7,z2,z3,z283,z4,z5,z6]),(0,[z284,z7,z43,z2,z3,z4,z5]),(0,[z7,z43,z2,z97,z4,z5,z6])]],
   [[(0,[z285,z7,z2,z3,z4,z5,z6]),(1,[z7,z43,z2,z3,z105,z5]),(0,[z7,z2,z3,z4,z286,z9,z6]),(0,[z287,z7,z43,z2,z3,z4,z5]),(0,[z7,z2,z3,z12,z4,z5,z24])],[(0,[z7,z2,z3,z4,z5,z213,z6]),(0,[z7,z43,z2,z79,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z288,z6]),(0,[z7,z2,z3,z4,z5,z289,z6]),(0,[z7,z2,z3,z4,z290,z5,z6])],[(0,[z7,z2,z3,z291,z4,z5,z6]),(0,[z197,z2,z3,z4,z5,z6,z73])],[(1,[z0,z83,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z29,z117,z6]),(0,[z7,z2,z3,z292,z4,z5,z6])],[(0,[z7,z2,z3,z4,z293,z5,z6]),(0,[z7,z2,z3,z96,z4,z29,z6]),(0,[z7,z2,z294,z3,z4,z216,z5]),(0,[z7,z63,z43,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z102,z5,z70]),(0,[z7,z2,z295,z3,z4,z5,z66]),(0,[z7,z2,z3,z4,z102,z5,z114])],[(0,[z146,z2,z3,z110,z4,z5,z6]),(0,[z107,z7,z2,z3,z4,z5,z60]),(0,[z7,z2,z296,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z297,z6])],[(0,[z7,z83,z3,z51,z4,z5,z6]),(0,[z7,z2,z298,z3,z4,z5,z6]),(0,[z7,z299,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z9,z60,z6]),(1,[z7,z43,z2,z3,z4,z9]),(0,[z7,z2,z3,z4,z5,z6,z300]),(0,[z7,z301,z2,z3,z4,z5,z6])],[(0,[z7,z302,z2,z3,z4,z5,z6]),(1,[z7,z2,z49,z3,z4,z114]),(0,[z7,z2,z49,z3,z4,z6,z114]),(0,[z7,z303,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z110,z4,z29,z6]),(0,[z7,z2,z3,z304,z4,z5,z6]),(0,[z7,z2,z3,z305,z4,z5,z6]),(0,[z7,z2,z306,z3,z4,z5,z6]),(0,[z7,z2,z294,z3,z4,z5,z6]),(0,[z7,z43,z2,z3,z4,z5,z297])],[(0,[z0,z7,z83,z3,z4,z5,z6]),(0,[z1,z7,z83,z3,z4,z5,z6]),(0,[z307,z7,z2,z3,z4,z5,z6]),(0,[z98,z7,z2,z3,z105,z5,z6]),(0,[z7,z308,z2,z3,z4,z29,z6]),(0,[z7,z2,z3,z12,z4,z100,z6]),(0,[z7,z2,z3,z309,z4,z5,z6])],[(0,[z147,z98,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z310,z5,z6]),(0,[z7,z2,z3,z4,z311,z5,z6]),(0,[z7,z2,z31,z3,z4,z29,z6]),(0,[z7,z312,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z313]),(0,[z7,z67,z2,z3,z4,z314,z6])],[(0,[z7,z2,z315,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z316,z5,z6]),(0,[z317,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z318,z5,z6]),(0,[z7,z142,z2,z3,z12,z4,z5]),(0,[z284,z7,z2,z3,z4,z5,z6])],[(0,[z319,z7,z2,z3,z4,z5,z6]),(0,[z287,z7,z2,z3,z4,z5,z6]),(0,[z7,z167,z2,z31,z4,z5,z6]),(0,[z7,z141,z2,z3,z4,z5,z32]),(0,[z7,z2,z3,z4,z320,z5,z6]),(0,[z7,z2,z3,z4,z321,z5,z6]),(0,[z7,z2,z3,z4,z5,z322,z6]),(0,[z7,z2,z3,z4,z14,z6,z114])],[(0,[z7,z2,z3,z4,z5,z323,z6]),(0,[z7,z2,z3,z240,z4,z5,z6]),(0,[z7,z324,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z65])],[(0,[z7,z133,z2,z3,z4,z9,z6]),(0,[z107,z197,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z325,z5,z6]),(0,[z7,z67,z31,z3,z4,z5,z6]),(0,[z326,z7,z2,z3,z4,z5,z6]),(0,[z7,z133,z2,z3,z4,z5,z135])],[(0,[z7,z2,z3,z4,z5,z6,z327]),(0,[z7,z2,z3,z4,z328,z5,z6]),(0,[z7,z2,z3,z4,z329,z5,z6]),(1,[z7,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z330,z6])]],
   [[(0,[z0,z7,z2,z3,z4,z5,z331]),(0,[z7,z2,z3,z4,z5,z331,z6]),(0,[z7,z2,z332,z3,z4,z5,z6]),(0,[z2,z3,z4,z29,z5,z9,z6]),(0,[z7,z333,z2,z3,z4,z5,z6]),(0,[z7,z63,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z334,z4,z5,z6])],[(0,[z7,z2,z64,z4,z5,z6,z65])],[(0,[z146,z7,z2,z3,z4,z5,z335]),(0,[z7,z2,z3,z336,z4,z9,z6]),(0,[z45,z7,z2,z3,z4,z29,z6]),(0,[z7,z93,z2,z3,z4,z29,z6]),(0,[z7,z93,z2,z79,z4,z5,z6]),(0,[z7,z43,z2,z155,z3,z4,z5])],[(0,[z1,z7,z2,z3,z4,z128,z6]),(0,[z7,z2,z173,z3,z4,z29,z6]),(0,[z7,z337,z2,z3,z4,z5,z6]),(0,[z7,z2,z338,z3,z4,z6,z65]),(0,[z7,z18,z2,z3,z5,z66,z6]),(0,[z7,z2,z3,z4,z5,z339,z6])],[(0,[z7,z2,z3,z4,z5,z6,z340]),(0,[z146,z7,z341,z3,z4,z5,z6]),(0,[z7,z2,z342,z3,z4,z5,z6]),(0,[z107,z7,z2,z3,z325,z5,z6]),(0,[z7,z2,z3,z4,z343,z5,z6]),(1,[z7,z43,z93,z2,z3,z5]),(1,[z7,z18,z2,z3,z66,z6])],[(0,[z7,z2,z79,z3,z4,z9,z6]),(0,[z7,z2,z3,z12,z4,z5,z66])],[(0,[z7,z2,z3,z4,z8,z5,z6]),(0,[z7,z2,z3,z4,z344,z5,z6]),(0,[z121,z7,z3,z4,z5,z297,z6]),(0,[z7,z2,z3,z4,z345,z5,z6]),(0,[z7,z2,z3,z217,z12,z4,z5])],[(0,[z7,z18,z2,z3,z4,z29,z6]),(0,[z7,z2,z346,z3,z4,z5,z6]),(0,[z347,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z13,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z6,z214]),(0,[z348,z7,z2,z3,z4,z5,z6]),(0,[z7,z349,z2,z3,z4,z5,z6]),(0,[z350,z7,z2,z3,z4,z5,z6])],[(0,[z1,z7,z2,z3,z12,z4,z5]),(0,[z30,z7,z2,z3,z4,z5,z6]),(0,[z7,z351,z2,z3,z4,z5,z6]),(0,[z16,z7,z2,z3,z5,z41,z6]),(0,[z7,z2,z3,z4,z352,z5,z6]),(0,[z7,z2,z240,z4,z13,z5,z6]),(0,[z7,z2,z3,z4,z20,z5,z6]),(0,[z7,z2,z3,z4,z172,z5,z6])],[(0,[z7,z353,z2,z3,z4,z5,z6]),(0,[z354,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z355,z3,z4,z5,z6]),(0,[z7,z133,z2,z3,z195,z4,z6]),(0,[z7,z2,z3,z4,z5,z6,z356]),(0,[z7,z2,z3,z4,z5,z6,z357])],[(0,[z7,z358,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z37,z5,z6]),(0,[z7,z2,z3,z359,z4,z37,z5]),(0,[z2,z3,z4,z5,z60,z6,z73]),(0,[z7,z2,z3,z4,z5,z297,z73]),(0,[z7,z2,z3,z4,z5,z6,z360]),(0,[z361,z7,z2,z3,z4,z5,z6]),(0,[z7,z67,z2,z31,z4,z5,z6]),(1,[z7,z2,z3,z362,z4,z5]),(0,[z7,z141,z3,z96,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z363,z6]),(1,[z7,z2,z3,z4,z100,z6])],[(0,[z7,z2,z3,z12,z4,z216,z5])],[(0,[z364,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z365,z4,z5,z6]),(0,[z7,z2,z366,z3,z4,z5,z6]),(0,[z7,z367,z2,z3,z4,z5,z6])],[(0,[z0,z7,z2,z3,z278,z5,z6]),(0,[z1,z7,z33,z3,z4,z5,z6]),(0,[z45,z58,z2,z3,z4,z5,z6]),(0,[z7,z2,z31,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z59,z6]),(0,[z16,z7,z43,z2,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z368,z6]),(0,[z7,z2,z3,z369,z4,z5,z6]),(0,[z7,z370,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z12,z4,z20,z5]),(0,[z7,z43,z371,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z5,z372,z6])],[(0,[z7,z2,z3,z373,z4,z5,z6]),(0,[z7,z374,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z375,z6]),(1,[z30,z2,z173,z4,z5,z6]),(0,[z7,z2,z3,z376,z4,z5,z6]),(0,[z7,z2,z3,z12,z4,z5,z6])],[],[(0,[z7,z2,z3,z4,z29,z6,z27])],[(0,[z1,z33,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z377,z6]),(0,[z7,z2,z378,z3,z4,z5,z6]),(1,[z7,z2,z19,z4,z21,z6]),(0,[z7,z2,z64,z3,z12,z4,z5]),(0,[z7,z2,z3,z4,z66,z14,z6])],[(1,[z7,z2,z3,z71,z5,z6]),(0,[z7,z2,z3,z4,z379,z5,z6]),(0,[z7,z380,z2,z3,z4,z5,z6]),(0,[z16,z7,z3,z4,z216,z5,z6]),(0,[z7,z381,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z382,z5,z6]),(0,[z7,z2,z3,z251,z12,z4,z5])],[(0,[z58,z7,z2,z3,z4,z9,z6]),(0,[z7,z61,z2,z3,z4,z9,z6]),(1,[z7,z43,z2,z3,z4,z29]),(1,[z7,z2,z3,z4,z383,z6]),(0,[z7,z43,z2,z3,z4,z5,z27]),(0,[z7,z2,z3,z4,z384,z5,z6])],[(0,[z7,z33,z2,z3,z12,z4,z5]),(0,[z385,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z386,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z387,z6]),(0,[z7,z141,z2,z3,z4,z5,z137]),(0,[z7,z2,z3,z12,z4,z5,z297]),(0,[z7,z2,z79,z3,z5,z41,z6]),(1,[z7,z43,z2,z3,z4,z5])],[(0,[z7,z2,z3,z4,z5,z166,z6]),(0,[z7,z2,z3,z4,z388,z5,z6]),(0,[z7,z2,z3,z4,z5,z389,z6]),(0,[z7,z257,z2,z3,z12,z4,z5]),(1,[z7,z2,z3,z12,z4,z100]),(0,[z7,z2,z3,z4,z5,z390,z6])]],
   [[(0,[z391,z7,z2,z3,z4,z5,z6]),(1,[z7,z249,z3,z4,z5,z6]),(0,[z7,z392,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z55,z29,z6]),(0,[z7,z2,z393,z3,z4,z5,z6]),(1,[z7,z394,z2,z3,z5,z6])],[(0,[z7,z2,z3,z4,z395,z5,z6]),(0,[z7,z2,z3,z4,z29,z396,z6]),(0,[z107,z7,z2,z3,z4,z5,z73])],[(0,[z7,z2,z3,z4,z5,z6,z397]),(0,[z7,z2,z3,z4,z398,z5,z6]),(0,[z399,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z400,z3,z4,z5,z6]),(0,[z7,z2,z3,z195,z206,z5,z6]),(0,[z7,z2,z401,z3,z4,z5,z6]),(0,[z7,z2,z3,z12,z4,z5,z109]),(0,[z7,z2,z3,z4,z5,z6,z114]),(0,[z7,z2,z3,z4,z5,z402,z6])],[(0,[z7,z2,z3,z4,z9,z6,z73]),(0,[z7,z18,z2,z3,z4,z9,z6])],[(1,[z1,z33,z3,z4,z5,z6]),(0,[z7,z2,z403,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z9,z77,z6]),(0,[z7,z2,z3,z4,z29,z404,z6]),(0,[z7,z167,z2,z3,z4,z5,z25]),(0,[z7,z2,z3,z4,z5,z405,z6])],[(0,[z0,z7,z2,z3,z4,z5,z6]),(0,[z146,z7,z2,z3,z12,z4,z5]),(1,[z7,z2,z3,z4,z210,z6])],[(0,[z98,z7,z2,z3,z4,z5,z166]),(0,[z7,z2,z3,z4,z5,z6,z406]),(0,[z7,z2,z3,z4,z407,z5,z6]),(0,[z7,z2,z408,z3,z4,z5,z6]),(0,[z7,z2,z3,z144,z4,z13,z5]),(1,[z7,z2,z79,z240,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z409]),(0,[z7,z2,z3,z5,z66,z41,z6]),(0,[z7,z2,z3,z4,z5,z6,z410])],[(0,[z30,z7,z2,z3,z4,z328,z6]),(0,[z7,z2,z38,z3,z4,z5,z6]),(0,[z147,z7,z2,z3,z4,z411,z6]),(0,[z7,z2,z3,z412,z4,z29,z6]),(0,[z7,z43,z2,z3,z4,z29,z5]),(0,[z7,z2,z3,z362,z4,z216,z5]),(0,[z7,z2,z413,z3,z4,z5,z6]),(0,[z7,z2,z230,z3,z4,z13,z5]),(1,[z7,z2,z97,z4,z5,z6])]],
   [[(0,[z7,z43,z2,z3,z12,z5,z6])],[(0,[z7,z2,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z414,z5,z6]),(0,[z7,z61,z2,z3,z195,z4,z6])],[(1,[z7,z2,z3,z4,z5,z6]),(0,[z107,z7,z2,z3,z4,z415,z6]),(0,[z7,z2,z3,z4,z5,z416,z6]),(0,[z7,z417,z2,z3,z4,z5,z6]),(0,[z7,z133,z2,z3,z4,z5,z237]),(0,[z7,z2,z3,z4,z418,z5,z6]),(0,[z7,z2,z3,z4,z102,z14,z6])],[(0,[z7,z2,z3,z4,z5,z411,z6]),(0,[z7,z2,z3,z105,z4,z9,z6]),(0,[z7,z419,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z29,z60,z6]),(0,[z7,z167,z3,z51,z4,z5,z6]),(0,[z7,z2,z3,z362,z4,z5,z6]),(0,[z7,z2,z3,z420,z4,z5,z6]),(0,[z7,z2,z19,z3,z4,z21,z6])],[(0,[z7,z2,z3,z4,z5,z21,z6]),(0,[z7,z2,z3,z4,z421,z5,z6])],[(1,[z7,z2,z3,z4,z422,z6]),(0,[z7,z2,z3,z4,z5,z26,z6]),(0,[z7,z423,z2,z3,z4,z5,z6])],[(0,[z146,z7,z2,z3,z4,z5,z424]),(0,[z146,z7,z167,z2,z4,z5,z6]),(0,[z7,z2,z3,z425,z4,z5,z6]),(0,[z7,z43,z141,z2,z3,z5,z6]),(0,[z121,z7,z43,z2,z3,z4,z5]),(0,[z7,z426,z43,z2,z3,z4,z5]),(0,[z427,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z428,z3,z4,z5,z6]),(0,[z197,z7,z2,z3,z4,z429,z6]),(0,[z430,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z431,z5,z6])]],
   [[(0,[z7,z432,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z433,z4,z5,z6]),(0,[z7,z18,z2,z3,z4,z206,z6]),(1,[z7,z43,z2,z3,z12,z5])],[(0,[z7,z2,z3,z4,z5,z434,z6]),(0,[z7,z2,z3,z435,z4,z5,z6]),(0,[z7,z2,z436,z3,z4,z5,z6]),(0,[z7,z437,z2,z3,z4,z5,z6]),(0,[z7,z142,z2,z3,z4,z117,z6]),(0,[z7,z3,z4,z5,z297,z6,z27])],[(0,[z7,z33,z2,z3,z4,z29,z6]),(0,[z7,z2,z438,z3,z4,z5,z6]),(0,[z7,z2,z439,z3,z4,z5,z6]),(0,[z7,z2,z3,z440,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z297,z60]),(0,[z7,z43,z167,z2,z3,z4,z5]),(0,[z441,z7,z2,z3,z4,z5,z6]),(0,[z442,z7,z2,z3,z4,z5,z6]),(0,[z7,z61,z2,z3,z4,z55,z6]),(0,[z7,z91,z2,z3,z4,z5,z6]),(0,[z7,z2,z443,z3,z4,z5,z6])],[(0,[z7,z33,z3,z51,z4,z5,z6]),(0,[z7,z2,z444,z3,z4,z5,z6]),(0,[z7,z133,z2,z19,z4,z5,z6]),(0,[z445,z7,z2,z3,z4,z5,z6])],[(0,[z58,z7,z43,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z55,z9,z6]),(0,[z7,z2,z3,z446,z4,z5,z6]),(0,[z7,z2,z3,z240,z12,z4,z5]),(0,[z7,z2,z3,z4,z5,z233,z6])],[(0,[z2,z173,z3,z110,z4,z5,z6]),(0,[z147,z7,z43,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z5,z429,z6]),(0,[z7,z447,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z115,z13,z6]),(0,[z7,z448,z2,z3,z4,z5,z6]),(0,[z7,z449,z43,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z102,z5,z6]),(0,[z7,z2,z3,z132,z102,z5,z6])],[(0,[z7,z2,z3,z51,z4,z29,z6]),(0,[z7,z2,z3,z4,z5,z6,z450])],[(0,[z7,z2,z3,z4,z451,z5,z6]),(0,[z7,z2,z3,z37,z5,z41,z6]),(0,[z7,z2,z3,z4,z452,z5,z6]),(0,[z7,z2,z3,z4,z453,z6,z27]),(0,[z7,z2,z3,z4,z5,z454,z6]),(0,[z7,z2,z3,z4,z5,z6,z455])]],
   [[(0,[z7,z2,z3,z456,z4,z5,z6]),(0,[z7,z91,z2,z3,z4,z5,z297])],[(0,[z7,z67,z2,z3,z4,z29,z6]),(0,[z7,z43,z2,z3,z4,z216,z5]),(0,[z7,z457,z2,z3,z4,z5,z6]),(0,[z7,z2,z152,z3,z4,z13,z6]),(0,[z7,z2,z19,z3,z4,z14,z6]),(0,[z7,z2,z3,z4,z5,z458,z6])],[(0,[z0,z7,z2,z3,z101,z5,z6]),(0,[z121,z7,z2,z3,z4,z5,z6]),(0,[z7,z459,z2,z3,z4,z5,z6]),(0,[z7,z2,z460,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z14,z6]),(0,[z7,z2,z3,z102,z5,z402,z6])],[(0,[z7,z2,z3,z4,z422,z5,z6]),(0,[z7,z2,z3,z4,z5,z461,z6]),(0,[z7,z2,z3,z12,z4,z5,z27]),(0,[z7,z43,z93,z2,z3,z4,z5]),(0,[z7,z43,z2,z3,z4,z20,z5]),(1,[z7,z2,z64,z4,z5,z65]),(0,[z7,z2,z3,z4,z5,z6,z24])],[(0,[z462,z7,z2,z3,z4,z5,z6]),(0,[z30,z7,z2,z3,z4,z463,z6]),(0,[z7,z2,z3,z105,z5,z41,z6]),(0,[z7,z7,z2,z3,z4,z29,z6]),(0,[z107,z7,z2,z3,z222,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z464])],[(1,[z7,z2,z87,z4,z5,z6]),(0,[z7,z2,z465,z3,z4,z5,z6]),(0,[z7,z93,z2,z3,z240,z5,z6]),(0,[z7,z43,z2,z79,z3,z4,z5]),(0,[z7,z466,z2,z3,z4,z5,z6]),(0,[z7,z43,z2,z3,z4,z5,z6])],[(1,[z7,z2,z3,z4,z5,z335]),(0,[z7,z167,z2,z3,z4,z9,z6]),(0,[z16,z7,z141,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z383,z216,z6]),(0,[z7,z2,z3,z4,z5,z453,z6]),(0,[z7,z467,z2,z3,z4,z5,z6]),(0,[z7,z43,z2,z3,z4,z4,z5])],[(1,[z7,z2,z3,z101,z5,z6]),(0,[z0,z7,z2,z3,z4,z395,z6]),(0,[z7,z2,z341,z3,z4,z5,z6]),(0,[z7,z2,z3,z468,z4,z5,z6]),(0,[z197,z7,z2,z3,z4,z5,z6])]],
   [[(1,[z7,z341,z3,z4,z5,z6]),(0,[z469,z7,z2,z3,z4,z5,z6]),(0,[z30,z7,z2,z3,z12,z4,z5]),(0,[z7,z2,z3,z4,z5,z470,z6]),(0,[z121,z7,z2,z3,z4,z5,z297]),(0,[z7,z2,z3,z4,z5,z6,z471])],[(0,[z472,z7,z2,z3,z4,z5,z6]),(0,[z147,z7,z2,z3,z4,z5,z6]),(0,[z7,z473,z2,z3,z4,z5,z6]),(0,[z7,z449,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z55,z206,z6]),(0,[z354,z7,z2,z3,z12,z4,z5])],[(0,[z7,z2,z474,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z475]),(0,[z7,z2,z3,z4,z5,z424,z6]),(0,[z476,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z396,z6]),(0,[z7,z2,z3,z4,z415,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z477])],[(0,[z16,z7,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z478,z4,z5,z6]),(0,[z7,z2,z3,z479,z4,z5,z6]),(0,[z7,z2,z480,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z481,z6]),(0,[z7,z2,z3,z4,z5,z482,z6]),(0,[z7,z2,z3,z4,z206,z14,z6])],[(0,[z7,z483,z2,z3,z4,z5,z6]),(0,[z147,z7,z2,z3,z4,z422,z6]),(0,[z7,z2,z19,z3,z4,z5,z6]),(0,[z7,z394,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z66,z6])],[(0,[z30,z7,z67,z2,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z5,z6]),(0,[z7,z2,z3,z12,z4,z29,z5]),(0,[z7,z2,z3,z4,z5,z484,z6]),(0,[z7,z142,z3,z4,z55,z5,z6]),(0,[z189,z7,z43,z2,z3,z4,z5])],[(0,[z7,z2,z122,z3,z4,z29,z6]),(0,[z7,z485,z2,z3,z4,z5,z6]),(0,[z7,z43,z2,z3,z195,z5,z6]),(0,[z7,z486,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6,z487]),(0,[z7,z43,z2,z3,z195,z4,z5]),(0,[z7,z2,z3,z12,z12,z4,z5]),(0,[z7,z2,z3,z376,z12,z4,z5])]],
   [[(0,[z7,z2,z83,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z488,z5,z6]),(0,[z7,z2,z3,z4,z5,z489,z6]),(0,[z7,z43,z2,z3,z4,z206,z5]),(0,[z7,z2,z3,z4,z490,z5,z6])],[(0,[z7,z2,z3,z4,z5,z491,z6]),(0,[z30,z7,z167,z2,z4,z5,z6]),(0,[z98,z7,z2,z3,z4,z245,z6]),(0,[z7,z2,z3,z4,z5,z492,z6]),(0,[z7,z493,z2,z3,z4,z5,z6])],[(0,[z494,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z51,z4,z9,z6]),(0,[z7,z2,z295,z3,z4,z5,z6])],[(0,[z7,z43,z2,z3,z37,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z495]),(0,[z7,z67,z167,z3,z4,z5,z6]),(1,[z7,z2,z444,z3,z4,z6]),(0,[z7,z63,z2,z79,z4,z5,z6]),(0,[z7,z2,z3,z496,z4,z5,z6]),(1,[z7,z2,z338,z3,z4,z6]),(0,[z7,z2,z338,z3,z4,z5,z6]),(0,[z497,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z498,z6])],[(0,[z98,z7,z2,z3,z4,z29,z6]),(0,[z7,z141,z2,z3,z4,z29,z6]),(0,[z7,z2,z3,z4,z29,z41,z6]),(0,[z7,z499,z2,z3,z4,z5,z6])],[(0,[z7,z500,z2,z3,z4,z5,z6]),(0,[z7,z67,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z73,z65]),(0,[z7,z2,z3,z12,z4,z5,z60]),(0,[z7,z43,z2,z155,z4,z5,z6])],[(0,[z7,z2,z3,z4,z9,z9,z6]),(0,[z107,z7,z2,z3,z4,z29,z6]),(0,[z7,z2,z3,z501,z4,z5,z6]),(0,[z7,z61,z2,z49,z3,z4,z6]),(0,[z7,z2,z3,z4,z502,z5,z6]),(0,[z7,z2,z3,z4,z206,z5,z6])],[(0,[z147,z7,z2,z3,z37,z5,z6]),(1,[z7,z43,z2,z3,z37,z5]),(0,[z7,z503,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z504,z5,z6]),(0,[z505,z7,z2,z3,z4,z5,z6])]],
   [[(1,[z7,z2,z3,z4,z5,z331]),(0,[z7,z2,z3,z4,z5,z506,z6]),(0,[z507,z7,z2,z3,z4,z5,z6]),(0,[z7,z7,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z29,z6,z73]),(0,[z7,z2,z3,z508,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z70,z6]),(0,[z7,z2,z3,z4,z509,z5,z6]),(0,[z7,z2,z3,z4,z281,z5,z6]),(0,[z510,z7,z2,z3,z4,z5,z6])],[(0,[z189,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z31,z110,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z314,z6]),(0,[z7,z2,z511,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z512,z6]),(0,[z513,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z514,z5,z6]),(0,[z7,z2,z49,z3,z12,z4,z5])],[(0,[z7,z2,z515,z3,z4,z5,z6]),(0,[z7,z516,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z13,z29,z6]),(0,[z7,z2,z3,z4,z5,z517,z6]),(0,[z7,z2,z19,z49,z3,z4,z6]),(0,[z7,z18,z133,z2,z3,z4,z6]),(1,[z7,z2,z3,z5,z243,z6])],[(0,[z7,z43,z2,z83,z3,z4,z5]),(1,[z7,z2,z3,z4,z411,z6]),(0,[z7,z2,z3,z96,z4,z9,z6]),(0,[z7,z518,z2,z3,z4,z5,z6]),(0,[z7,z43,z2,z3,z4,z5,z73]),(0,[z7,z2,z3,z4,z5,z519,z6]),(0,[z7,z2,z3,z4,z5,z520,z6]),(0,[z7,z2,z64,z3,z4,z5,z65]),(0,[z7,z2,z3,z4,z206,z5,z458])],[(0,[z0,z7,z2,z3,z12,z4,z5]),(0,[z30,z7,z2,z3,z4,z29,z6]),(0,[z7,z2,z3,z4,z20,z29,z6]),(1,[z16,z7,z43,z2,z3,z5]),(0,[z7,z521,z2,z3,z4,z5,z6])],[(0,[z197,z7,z2,z3,z4,z5,z73]),(0,[z7,z91,z2,z3,z4,z5,z27]),(0,[z522,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z206,z5,z523]),(0,[z7,z524,z43,z2,z3,z4,z5])],[(0,[z525,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z31,z173,z4,z5,z6]),(0,[z7,z2,z3,z4,z37,z29,z6]),(0,[z7,z2,z3,z240,z37,z5,z6]),(1,[z58,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z70,z297]),(0,[z7,z2,z3,z526,z4,z5,z6])],[(0,[z7,z2,z3,z110,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z140,z6]),(0,[z7,z2,z3,z4,z5,z527,z6]),(0,[z7,z2,z3,z4,z115,z5,z6])]],
   [[(0,[z7,z302,z2,z83,z4,z5,z6]),(0,[z7,z2,z3,z4,z528,z5,z6]),(1,[z7,z2,z3,z12,z4,z29]),(1,[z7,z2,z294,z3,z4,z5])],[(0,[z0,z7,z33,z3,z4,z5,z6]),(0,[z7,z266,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z529,z4,z5,z6]),(0,[z7,z2,z3,z4,z179,z29,z6]),(0,[z7,z2,z3,z4,z5,z6,z530])],[(0,[z7,z2,z3,z4,z531,z5,z6]),(0,[z7,z142,z2,z3,z4,z29,z6]),(1,[z7,z2,z3,z4,z5,z532]),(0,[z7,z43,z2,z31,z3,z4,z5]),(0,[z16,z7,z43,z2,z3,z4,z5])],[(0,[z533,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z6]),(0,[z7,z2,z3,z4,z5,z534,z6]),(0,[z7,z2,z152,z3,z4,z5,z6]),(0,[z7,z2,z3,z12,z4,z102,z5])],[(0,[z7,z18,z61,z2,z3,z4,z6]),(0,[z7,z2,z3,z4,z5,z535,z6]),(0,[z7,z2,z3,z4,z5,z536,z6]),(0,[z7,z2,z3,z12,z4,z4,z5])],[(1,[z7,z2,z3,z4,z429,z6]),(0,[z121,z7,z2,z3,z4,z5,z27])],[(1,[z7,z2,z3,z278,z5,z6]),(0,[z537,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z286,z5,z6]),(0,[z7,z2,z19,z3,z4,z117,z6]),(0,[z7,z133,z2,z3,z4,z55,z6]),(0,[z40,z7,z43,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z5,z538,z6])],[(0,[z7,z2,z3,z195,z4,z29,z6]),(0,[z7,z2,z3,z4,z5,z117,z6]),(0,[z7,z2,z3,z4,z5,z6,z539])]],
   [[(0,[z7,z2,z3,z4,z540,z5,z6]),(0,[z98,z7,z2,z3,z4,z9,z6]),(0,[z7,z141,z2,z3,z4,z9,z6]),(0,[z7,z125,z2,z3,z5,z6,z27])],[(0,[z541,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z542]),(0,[z7,z93,z2,z3,z4,z9,z6]),(0,[z45,z7,z2,z3,z4,z9,z6]),(0,[z543,z7,z2,z3,z4,z5,z6]),(1,[z7,z67,z31,z4,z5,z6]),(0,[z16,z7,z2,z3,z4,z210,z6]),(1,[z7,z61,z3,z4,z117,z6]),(0,[z7,z91,z2,z3,z12,z4,z5]),(0,[z7,z133,z2,z3,z4,z14,z6]),(0,[z544,z7,z2,z3,z4,z5,z6]),(0,[z7,z524,z2,z3,z4,z5,z6])],[(1,[z7,z2,z3,z4,z5,z424]),(0,[z7,z2,z173,z3,z4,z9,z6]),(0,[z107,z7,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z9,z6,z267]),(0,[z7,z208,z2,z3,z4,z29,z6]),(0,[z7,z2,z3,z4,z5,z545,z6]),(0,[z7,z2,z546,z3,z4,z5,z6]),(0,[z547,z7,z2,z3,z4,z5,z6])],[(0,[z7,z22,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z29,z148,z6]),(0,[z197,z7,z2,z3,z4,z548,z6]),(0,[z7,z2,z3,z4,z5,z32,z6])],[(0,[z7,z2,z3,z4,z549,z5,z6]),(0,[z7,z2,z3,z4,z9,z273,z6]),(0,[z7,z550,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z551,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z297,z65]),(0,[z7,z447,z2,z3,z12,z4,z5])],[(0,[z146,z7,z2,z3,z4,z72,z6]),(0,[z7,z2,z3,z4,z216,z29,z6]),(0,[z7,z2,z49,z3,z4,z29,z6]),(0,[z7,z552,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z553]),(0,[z7,z2,z3,z12,z4,z5,z117]),(0,[z7,z2,z3,z554,z4,z5,z6]),(0,[z7,z2,z3,z12,z195,z4,z5]),(0,[z7,z2,z3,z12,z4,z100,z5])],[(0,[z7,z2,z555,z3,z4,z5,z6]),(0,[z146,z7,z2,z3,z4,z209,z6]),(0,[z7,z2,z3,z37,z216,z5,z6]),(0,[z7,z2,z3,z4,z5,z70,z73]),(0,[z7,z43,z2,z3,z96,z4,z5]),(1,[z7,z2,z3,z4,z453,z6]),(0,[z7,z2,z3,z12,z4,z206,z5]),(0,[z7,z2,z3,z4,z556,z5,z6]),(0,[z7,z557,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z29,z29,z6]),(0,[z7,z2,z3,z558,z4,z5,z6]),(0,[z7,z559,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z2,z3,z4,z29,z6]),(0,[z7,z2,z3,z4,z206,z117,z6]),(0,[z7,z2,z3,z4,z560,z5,z6]),(1,[z7,z2,z3,z4,z5,z561]),(0,[z7,z2,z562,z3,z4,z5,z6])],[(0,[z7,z2,z563,z3,z4,z5,z6]),(1,[z98,z2,z3,z105,z5,z6]),(0,[z58,z2,z3,z4,z5,z9,z6]),(0,[z7,z564,z2,z3,z4,z5,z6]),(0,[z121,z7,z2,z3,z12,z4,z5])],[(0,[z7,z565,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z566,z6]),(0,[z7,z43,z133,z2,z3,z4,z5])],[(0,[z7,z2,z3,z105,z216,z5,z6]),(0,[z7,z2,z3,z4,z5,z567,z6]),(1,[z7,z43,z141,z2,z3,z5]),(0,[z7,z2,z568,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z569]),(0,[z7,z2,z3,z570,z4,z5,z6]),(0,[z7,z2,z3,z12,z4,z109,z6])],[(0,[z0,z7,z2,z3,z4,z491,z6]),(0,[z7,z2,z571,z3,z4,z5,z6]),(0,[z7,z572,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z9,z297,z6]),(0,[z7,z167,z2,z51,z4,z5,z6]),(0,[z7,z2,z573,z3,z4,z5,z6]),(0,[z7,z2,z444,z3,z4,z6,z27]),(0,[z7,z574,z2,z3,z4,z5,z6]),(0,[z7,z133,z2,z3,z4,z5,z6]),(0,[z7,z43,z2,z3,z12,z4,z5])],[(0,[z146,z7,z67,z2,z4,z5,z6]),(1,[z7,z186,z2,z3,z4,z5]),(0,[z575,z7,z2,z3,z4,z5,z6]),(0,[z121,z7,z91,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z241,z6]),(0,[z576,z7,z43,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z5,z41,z6])],[(0,[z7,z2,z3,z4,z577,z5,z6]),(0,[z7,z142,z2,z3,z4,z9,z6]),(0,[z197,z7,z2,z3,z12,z4,z5]),(1,[z7,z2,z3,z325,z5,z6]),(1,[z7,z142,z3,z4,z55,z6]),(0,[z578,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z79,z3,z4,z5,z561])],[(0,[z7,z2,z3,z4,z5,z6,z335]),(0,[z7,z579,z2,z3,z4,z5,z6]),(0,[z7,z43,z2,z3,z4,z37,z5]),(0,[z7,z2,z3,z4,z5,z6,z580]),(0,[z7,z2,z3,z4,z581,z5,z6]),(0,[z7,z582,z2,z3,z4,z5,z6]),(0,[z7,z583,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z7,z2,z88,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z463,z6]),(0,[z147,z7,z2,z3,z12,z4,z5]),(0,[z7,z2,z3,z336,z4,z5,z6]),(0,[z7,z371,z2,z3,z4,z5,z6])],[(1,[z7,z2,z3,z4,z491,z6]),(0,[z7,z2,z3,z12,z4,z5,z73]),(0,[z7,z43,z67,z2,z3,z4,z5]),(0,[z7,z381,z2,z3,z4,z216,z6]),(0,[z7,z141,z2,z3,z5,z41,z6])],[(0,[z584,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z64,z3,z4,z29,z6]),(0,[z107,z7,z2,z3,z4,z182,z6]),(0,[z7,z43,z2,z3,z4,z5,z60]),(0,[z7,z43,z141,z2,z3,z4,z5]),(0,[z7,z93,z2,z3,z5,z41,z6]),(0,[z7,z63,z2,z4,z13,z5,z6]),(0,[z7,z2,z3,z4,z585,z5,z6]),(0,[z586,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z458]),(0,[z7,z2,z3,z4,z5,z6,z587])],[(0,[z588,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z195,z4,z9,z6]),(1,[z7,z381,z2,z3,z4,z6]),(0,[z7,z2,z3,z4,z5,z70,z27]),(1,[z121,z7,z3,z4,z5,z297]),(0,[z7,z2,z79,z3,z4,z5,z6]),(0,[z7,z2,z19,z3,z12,z4,z5]),(0,[z7,z43,z2,z3,z5,z6,z24])],[(0,[z7,z589,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z590,z4,z5,z6]),(0,[z7,z2,z3,z4,z9,z6,z65]),(0,[z197,z7,z2,z3,z4,z5,z60]),(0,[z7,z43,z61,z2,z3,z4,z5]),(0,[z7,z2,z591,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z523]),(0,[z7,z43,z2,z168,z3,z4,z5])],[(0,[z7,z2,z3,z4,z92,z5,z6]),(0,[z7,z2,z3,z4,z5,z592,z6]),(0,[z7,z2,z593,z3,z4,z5,z6]),(0,[z594,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z9,z330,z6]),(0,[z7,z595,z2,z3,z4,z5,z6]),(0,[z7,z61,z3,z4,z5,z117,z6]),(0,[z596,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z155,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z597])],[(0,[z7,z2,z83,z3,z12,z4,z5])]],
   [[(1,[z7,z302,z2,z4,z5,z6]),(0,[z1,z7,z2,z3,z4,z118,z6]),(0,[z598,z7,z2,z3,z4,z5,z6]),(0,[z7,z43,z2,z3,z105,z5,z6]),(0,[z45,z7,z43,z2,z3,z4,z5]),(0,[z599,z7,z2,z3,z4,z5,z6]),(0,[z7,z61,z2,z3,z4,z14,z6]),(0,[z7,z2,z3,z4,z5,z600,z6])],[(0,[z33,z2,z83,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z216,z9,z6]),(0,[z7,z2,z3,z4,z29,z6,z212]),(1,[z7,z2,z3,z4,z314,z6]),(0,[z7,z601,z2,z3,z4,z5,z6]),(0,[z602,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z603]),(0,[z7,z2,z3,z4,z5,z6,z604]),(0,[z576,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z605]),(0,[z11,z7,z2,z3,z4,z5,z6])],[(0,[z98,z7,z2,z3,z4,z213,z6]),(0,[z7,z2,z3,z4,z269,z29,z6]),(0,[z7,z142,z2,z3,z195,z4,z6]),(0,[z606,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z607,z5,z6]),(0,[z7,z133,z2,z49,z3,z4,z6]),(0,[z7,z63,z2,z3,z12,z4,z5]),(0,[z7,z2,z3,z496,z12,z4,z5]),(1,[z7,z2,z3,z4,z102,z14])],[(0,[z7,z2,z3,z4,z608,z5,z6]),(0,[z7,z2,z110,z51,z4,z5,z6]),(0,[z7,z2,z3,z4,z29,z9,z6]),(0,[z7,z308,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z609,z6]),(0,[z7,z2,z3,z610,z4,z5,z6]),(0,[z611,z7,z2,z3,z4,z5,z6])],[(0,[z1,z7,z2,z3,z4,z9,z6]),(0,[z146,z7,z2,z3,z4,z29,z6]),(0,[z147,z7,z2,z3,z105,z5,z6]),(1,[z7,z2,z3,z12,z4,z9]),(0,[z7,z2,z31,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z612,z5,z6]),(0,[z7,z43,z2,z3,z5,z66,z6]),(0,[z613,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z614,z3,z4,z5,z6])],[(0,[z7,z426,z2,z3,z4,z5,z6]),(0,[z7,z2,z79,z3,z13,z5,z6]),(0,[z7,z2,z3,z615,z4,z5,z6]),(0,[z7,z18,z43,z2,z3,z4,z5]),(1,[z7,z2,z155,z4,z5,z6]),(1,[z7,z2,z3,z4,z109,z6])],[(0,[z616,z7,z2,z3,z4,z5,z6]),(1,[z197,z2,z3,z4,z5,z73]),(0,[z7,z617,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z618,z5,z6]),(0,[z7,z2,z3,z619,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z27])],[(0,[z7,z43,z2,z3,z4,z13,z5]),(0,[z7,z2,z3,z12,z4,z5,z65])]],
   [[(0,[z7,z620,z2,z3,z4,z5,z6]),(0,[z2,z3,z105,z4,z37,z5,z6]),(0,[z7,z43,z2,z3,z4,z29,z6]),(0,[z7,z621,z2,z3,z4,z5,z6]),(1,[z7,z91,z3,z4,z5,z27]),(0,[z7,z2,z3,z195,z4,z206,z6]),(0,[z7,z43,z2,z3,z4,z102,z5]),(0,[z7,z2,z3,z4,z5,z6,z622]),(0,[z189,z7,z2,z3,z12,z4,z5])],[(0,[z7,z43,z2,z3,z4,z5,z9]),(0,[z7,z2,z3,z4,z5,z532,z6]),(0,[z7,z2,z3,z4,z623,z5,z6])],[(0,[z197,z7,z2,z3,z4,z29,z6]),(0,[z7,z2,z3,z624,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z625,z6]),(0,[z626,z7,z2,z3,z4,z5,z6]),(1,[z7,z43,z2,z3,z195,z5])],[(1,[z7,z2,z3,z4,z328,z6]),(0,[z7,z2,z3,z240,z105,z5,z6]),(0,[z58,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z627,z3,z4,z5,z6]),(0,[z16,z7,z2,z3,z216,z5,z6]),(0,[z7,z61,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z628,z5,z6])],[(0,[z7,z2,z3,z4,z5,z629,z6]),(0,[z7,z630,z2,z3,z4,z5,z6]),(0,[z45,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z12,z96,z4,z5]),(0,[z7,z2,z3,z4,z631,z5,z6]),(0,[z7,z2,z3,z195,z5,z41,z6])],[(0,[z7,z2,z173,z3,z4,z5,z6]),(0,[z7,z2,z632,z3,z4,z5,z6]),(0,[z7,z43,z2,z3,z110,z4,z5]),(0,[z633,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z70,z60]),(0,[z7,z2,z3,z4,z5,z6,z634]),(0,[z635,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z636,z3,z4,z5,z6])],[(0,[z7,z2,z637,z3,z4,z5,z6]),(0,[z7,z2,z64,z3,z4,z9,z6]),(0,[z7,z2,z49,z3,z4,z206,z6])],[(1,[z7,z2,z3,z4,z395,z6]),(0,[z7,z2,z638,z3,z4,z5,z6]),(0,[z7,z91,z3,z4,z5,z6,z27]),(0,[z7,z2,z4,z13,z5,z6,z65]),(0,[z7,z639,z2,z3,z4,z5,z6]),(0,[z7,z394,z2,z3,z5,z6,z65]),(0,[z7,z2,z3,z640,z4,z5,z6])]],
   [[(0,[z7,z312,z2,z3,z4,z29,z6]),(0,[z7,z2,z3,z4,z5,z404,z6]),(0,[z7,z641,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z642,z4,z5,z6]),(0,[z7,z2,z19,z4,z5,z21,z6]),(0,[z7,z2,z3,z643,z4,z5,z6]),(0,[z7,z18,z2,z3,z4,z66,z6]),(0,[z7,z2,z3,z4,z5,z644,z6]),(0,[z7,z2,z3,z4,z5,z645,z6])],[(0,[z7,z33,z2,z3,z4,z9,z6]),(0,[z7,z2,z49,z3,z4,z5,z65]),(0,[z7,z18,z2,z3,z4,z5,z6])],[(0,[z7,z2,z403,z3,z4,z5,z6]),(0,[z7,z43,z2,z3,z4,z5,z117]),(1,[z7,z2,z3,z5,z402,z6])],[(0,[z7,z2,z83,z3,z4,z29,z6]),(0,[z646,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z240,z4,z29,z6]),(0,[z7,z2,z3,z4,z647,z5,z6])],[(0,[z648,z7,z2,z3,z4,z5,z6]),(0,[z7,z649,z2,z3,z4,z5,z6]),(0,[z7,z650,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z415,z6]),(0,[z7,z2,z3,z4,z651,z5,z6]),(1,[z7,z43,z2,z3,z5,z66]),(0,[z7,z43,z2,z3,z4,z5,z262])],[(0,[z7,z2,z3,z12,z4,z37,z5]),(0,[z7,z3,z96,z4,z216,z5,z6]),(0,[z7,z2,z3,z4,z652,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6,z653]),(0,[z113,z7,z2,z3,z4,z5,z6]),(0,[z7,z63,z2,z3,z4,z29,z6]),(0,[z7,z2,z654,z3,z4,z5,z6]),(0,[z16,z7,z2,z3,z96,z5,z6]),(0,[z7,z2,z3,z4,z117,z66,z6]),(1,[z7,z2,z230,z3,z4,z5]),(0,[z7,z2,z3,z12,z238,z4,z5])],[(0,[z7,z2,z3,z655,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z60,z6]),(0,[z7,z2,z3,z656,z4,z5,z6]),(0,[z7,z2,z3,z4,z657,z5,z6]),(0,[z7,z2,z3,z4,z5,z658,z6])]],
   [[(0,[z146,z7,z2,z3,z4,z9,z6]),(0,[z7,z2,z173,z51,z4,z5,z6]),(0,[z7,z2,z79,z240,z4,z5,z6]),(0,[z7,z2,z79,z4,z5,z6,z65])],[(0,[z659,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z105,z4,z5,z6]),(0,[z7,z419,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z9,z6,z114]),(0,[z7,z2,z3,z4,z206,z29,z6]),(1,[z7,z2,z3,z4,z548,z6]),(0,[z7,z167,z2,z3,z4,z5,z532]),(0,[z7,z2,z3,z4,z5,z660,z6])],[(0,[z661,z7,z2,z3,z4,z5,z6]),(0,[z7,z662,z2,z3,z4,z5,z6]),(0,[z7,z18,z2,z3,z195,z5,z6])],[(1,[z7,z2,z3,z4,z5,z134]),(1,[z7,z2,z3,z4,z123,z6]),(0,[z7,z2,z3,z4,z5,z6,z663]),(0,[z7,z43,z2,z3,z4,z55,z5]),(0,[z7,z2,z49,z3,z4,z5,z14])],[(0,[z664,z7,z2,z3,z4,z5,z6]),(0,[z665,z7,z2,z3,z4,z5,z6])],[(0,[z7,z666,z2,z3,z4,z5,z6]),(0,[z667,z7,z2,z3,z4,z5,z6]),(0,[z7,z516,z2,z3,z4,z29,z6]),(0,[z668,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z52,z6]),(0,[z7,z2,z3,z4,z5,z669,z6]),(1,[z7,z2,z3,z5,z26,z6]),(0,[z7,z133,z2,z4,z20,z5,z6]),(1,[z7,z2,z3,z4,z241,z6])],[(1,[z7,z2,z3,z4,z128,z6]),(0,[z7,z2,z3,z180,z4,z5,z6]),(0,[z7,z2,z3,z37,z13,z5,z6]),(1,[z45,z2,z3,z4,z29,z6]),(0,[z7,z133,z2,z3,z4,z21,z6]),(0,[z7,z2,z3,z4,z5,z6,z670])],[(0,[z0,z7,z2,z3,z4,z5,z214]),(0,[z7,z2,z3,z222,z4,z5,z6]),(0,[z671,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z157,z6])]],
   [[(0,[z7,z2,z3,z672,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z118,z6]),(0,[z7,z249,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z463,z6]),(0,[z7,z299,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z673,z6]),(0,[z7,z2,z3,z4,z5,z109,z6])],[(0,[z674,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z72,z6]),(0,[z7,z2,z3,z4,z29,z297,z6]),(0,[z7,z675,z2,z3,z4,z5,z6]),(0,[z7,z31,z3,z51,z4,z5,z6]),(0,[z676,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z55,z66,z6]),(0,[z7,z2,z3,z4,z5,z6,z561]),(0,[z677,z7,z43,z2,z3,z4,z5])],[(0,[z678,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z209,z6]),(0,[z7,z2,z3,z4,z55,z5,z6]),(0,[z7,z2,z3,z679,z4,z5,z6]),(0,[z7,z680,z2,z3,z4,z5,z6])],[(0,[z7,z2,z88,z3,z4,z5,z6]),(0,[z7,z2,z3,z105,z13,z5,z6]),(0,[z7,z2,z3,z4,z9,z21,z6]),(0,[z7,z2,z3,z4,z5,z6,z681]),(0,[z7,z682,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z683,z6]),(0,[z7,z2,z3,z4,z684,z5,z6]),(0,[z7,z2,z19,z3,z4,z20,z6]),(0,[z7,z2,z3,z12,z4,z5,z21])],[(0,[z7,z2,z3,z4,z310,z9,z6]),(0,[z7,z2,z3,z4,z311,z9,z6]),(0,[z7,z2,z3,z4,z102,z5,z65]),(1,[z7,z2,z3,z12,z4,z5])],[(1,[z7,z2,z3,z359,z4,z5]),(0,[z7,z2,z3,z4,z531,z29,z6]),(0,[z7,z61,z2,z3,z4,z117,z6]),(0,[z7,z2,z3,z4,z685,z5,z6]),(0,[z7,z2,z3,z12,z4,z13,z5]),(0,[z7,z2,z3,z4,z5,z6,z686])],[(0,[z147,z2,z3,z4,z37,z5,z6]),(0,[z7,z2,z3,z687,z4,z5,z6]),(0,[z7,z2,z3,z359,z4,z5,z6]),(0,[z7,z2,z3,z12,z4,z29,z6]),(0,[z7,z2,z3,z4,z5,z688,z6]),(0,[z7,z2,z689,z3,z4,z5,z6]),(0,[z7,z690,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z240,z4,z9,z6]),(0,[z7,z2,z3,z12,z4,z5,z9]),(0,[z7,z691,z2,z3,z4,z5,z6]),(0,[z7,z2,z692,z3,z4,z5,z6])]],
   [[(0,[z146,z7,z2,z3,z180,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z693]),(1,[z7,z2,z295,z3,z4,z5])],[(0,[z98,z2,z3,z105,z4,z5,z6]),(0,[z7,z2,z3,z4,z29,z6,z65]),(0,[z7,z2,z3,z412,z4,z5,z6]),(0,[z7,z2,z3,z4,z548,z5,z6]),(0,[z7,z2,z3,z144,z4,z5,z6]),(0,[z7,z694,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z5,z243,z6,z65]),(0,[z7,z2,z3,z4,z5,z695,z6])],[(0,[z7,z2,z696,z3,z4,z5,z6]),(0,[z7,z2,z79,z3,z12,z4,z5]),(0,[z7,z2,z3,z4,z697,z5,z6]),(0,[z7,z43,z2,z3,z4,z201,z5]),(0,[z7,z2,z3,z97,z4,z5,z6]),(0,[z7,z2,z176,z3,z4,z5,z6])],[(0,[z7,z186,z2,z3,z4,z5,z6])],[(0,[z698,z7,z2,z3,z4,z5,z6]),(0,[z7,z167,z2,z3,z4,z5,z6]),(0,[z7,z125,z2,z3,z4,z5,z6]),(0,[z7,z43,z2,z64,z3,z4,z5]),(0,[z7,z43,z2,z3,z4,z5,z65])],[(0,[z146,z7,z2,z3,z71,z5,z6]),(0,[z677,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z699,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z233]),(0,[z7,z2,z3,z4,z5,z6,z523])],[(1,[z146,z2,z110,z4,z5,z6]),(0,[z700,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z342,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z383,z5,z6]),(0,[z701,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z702,z5,z6]),(0,[z7,z2,z49,z3,z4,z5,z70]),(0,[z7,z2,z3,z703,z4,z5,z6]),(0,[z7,z2,z49,z3,z4,z5,z114]),(0,[z704,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z705,z3,z4,z5,z6]),(0,[z706,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z237,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z7,z141,z3,z96,z9,z6]),(0,[z2,z3,z4,z9,z688,z6]),(0,[z7,z2,z3,z707,z5,z6]),(0,[z7,z2,z3,z4,z708,z6])],[(0,[z7,z2,z3,z4,z709,z6]),(0,[z7,z2,z3,z4,z710,z6]),(0,[z7,z2,z3,z144,z4,z29]),(0,[z7,z43,z93,z2,z155,z5]),(0,[z7,z43,z2,z591,z3,z5])],[(0,[z7,z2,z711,z3,z4,z6]),(0,[z7,z2,z4,z5,z157,z65]),(0,[z7,z2,z79,z240,z5,z157])],[(0,[z7,z43,z2,z155,z4,z29]),(0,[z7,z2,z3,z712,z4,z5])],[(0,[z7,z2,z3,z713,z5,z6]),(0,[z16,z7,z43,z2,z3,z210]),(0,[z7,z43,z2,z79,z155,z5]),(0,[z7,z43,z2,z155,z4,z5])],[(0,[z7,z2,z3,z4,z714,z6])],[(0,[z7,z2,z3,z4,z395,z6]),(0,[z7,z249,z3,z180,z5,z6]),(0,[z7,z67,z31,z4,z123,z6]),(0,[z7,z43,z2,z94,z3,z5]),(0,[z7,z449,z371,z3,z4,z5])],[(0,[z7,z43,z2,z3,z222,z5]),(0,[z7,z2,z3,z4,z5,z715]),(0,[z716,z2,z3,z4,z5,z6]),(0,[z7,z142,z3,z4,z717,z6]),(0,[z7,z10,z2,z97,z4,z5])],[],[(0,[z7,z2,z3,z4,z5,z166]),(0,[z7,z43,z2,z3,z656,z5]),(0,[z7,z524,z2,z3,z4,z201])],[(0,[z7,z43,z2,z88,z4,z5]),(0,[z7,z2,z3,z4,z718,z6]),(0,[z7,z2,z19,z554,z4,z6]),(0,[z7,z2,z719,z4,z5,z6])],[(0,[z7,z2,z720,z4,z5,z6]),(0,[z7,z2,z97,z4,z201,z5])],[(0,[z7,z2,z3,z278,z5,z214]),(0,[z7,z2,z3,z721,z5,z6]),(0,[z722,z83,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z723,z6]),(0,[z7,z2,z3,z325,z415,z6]),(0,[z7,z2,z3,z4,z724,z6]),(0,[z7,z2,z3,z12,z4,z52]),(0,[z7,z63,z2,z4,z281,z5]),(0,[z7,z2,z3,z4,z102,z109])],[(0,[z7,z2,z3,z4,z72,z424]),(0,[z7,z2,z230,z3,z4,z5])],[(0,[z7,z249,z3,z4,z72,z6]),(0,[z7,z2,z3,z4,z209,z424]),(0,[z7,z18,z2,z3,z148,z6])],[(0,[z7,z2,z3,z12,z4,z491]),(0,[z7,z725,z3,z4,z5,z6]),(0,[z16,z7,z3,z216,z9,z6]),(0,[z7,z2,z3,z726,z4,z5]),(0,[z7,z43,z2,z727,z4,z5])]],
   [[(0,[z7,z2,z3,z728,z5,z6]),(0,[z7,z2,z3,z4,z729,z6]),(0,[z7,z2,z3,z4,z5,z730]),(0,[z7,z43,z2,z3,z5,z402])],[(0,[z7,z2,z3,z4,z731,z6]),(0,[z146,z2,z110,z12,z4,z5])],[(0,[z7,z2,z3,z4,z29,z331]),(0,[z7,z2,z3,z4,z732,z6]),(0,[z7,z2,z3,z4,z5,z733])],[(0,[z7,z2,z87,z4,z9,z6]),(0,[z7,z2,z734,z4,z5,z6]),(0,[z354,z7,z3,z4,z172,z5])],[(0,[z7,z2,z3,z4,z52,z6]),(0,[z16,z7,z2,z294,z3,z5]),(0,[z7,z2,z3,z5,z26,z6])],[(0,[z7,z2,z735,z4,z5,z6]),(0,[z45,z2,z3,z4,z29,z6]),(0,[z7,z43,z2,z3,z4,z415]),(0,[z7,z2,z3,z4,z736,z6]),(0,[z7,z43,z2,z3,z420,z5]),(0,[z7,z394,z2,z79,z5,z6]),(0,[z7,z2,z3,z195,z737,z6])],[(0,[z7,z2,z3,z4,z5,z738]),(0,[z7,z2,z3,z4,z739,z6]),(0,[z7,z43,z2,z155,z12,z5])],[(0,[z7,z2,z3,z4,z740,z6]),(0,[z7,z2,z3,z4,z92,z59])],[(0,[z7,z2,z3,z741,z5,z6]),(0,[z7,z43,z2,z97,z4,z29]),(0,[z7,z466,z3,z4,z117,z6]),(0,[z7,z43,z2,z3,z5,z243])],[(0,[z7,z2,z3,z4,z742,z6]),(0,[z2,z3,z743,z37,z5,z6]),(0,[z7,z43,z2,z3,z251,z5]),(0,[z7,z43,z2,z97,z4,z5])],[(0,[z7,z2,z88,z4,z5,z331]),(0,[z7,z744,z2,z4,z5,z6]),(0,[z146,z2,z110,z4,z5,z424]),(0,[z7,z18,z2,z3,z628,z6])],[(0,[z7,z2,z3,z745,z5,z6]),(0,[z7,z2,z746,z3,z4,z6]),(0,[z7,z2,z747,z3,z4,z6]),(0,[z7,z2,z748,z3,z4,z6]),(0,[z7,z2,z3,z195,z206,z458])],[(0,[z7,z2,z3,z12,z4,z453]),(0,[z7,z2,z3,z4,z749,z6])],[(0,[z7,z2,z3,z222,z5,z6]),(0,[z7,z2,z3,z4,z750,z6])],[(0,[z7,z2,z3,z751,z5,z6]),(0,[z7,z2,z3,z752,z4,z5])],[(0,[z0,z302,z83,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z753])]],
   [[(0,[z7,z754,z3,z4,z5,z6]),(0,[z7,z380,z2,z3,z12,z5]),(0,[z7,z43,z265,z2,z3,z5]),(0,[z7,z447,z394,z2,z3,z5]),(0,[z7,z43,z2,z3,z4,z100])],[(0,[z7,z43,z2,z155,z105,z5])],[(0,[z7,z2,z3,z4,z755,z6])],[(0,[z7,z2,z3,z12,z4,z245]),(0,[z2,z3,z4,z5,z756,z73]),(0,[z7,z43,z211,z2,z3,z5])],[(0,[z7,z2,z3,z180,z5,z335]),(0,[z7,z3,z4,z757,z5,z6]),(0,[z7,z31,z758,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z237])],[(0,[z7,z2,z3,z759,z5,z6]),(0,[z598,z7,z43,z2,z3,z5]),(0,[z7,z2,z3,z144,z4,z9]),(0,[z7,z43,z2,z3,z117,z66])],[(0,[z7,z302,z2,z12,z4,z5]),(0,[z30,z43,z2,z173,z4,z5]),(0,[z284,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z760,z6])],[(0,[z7,z2,z3,z4,z761,z6]),(0,[z7,z2,z3,z4,z762,z6]),(0,[z7,z3,z4,z5,z763,z27]),(0,[z7,z2,z3,z12,z4,z764])],[(0,[z7,z2,z3,z765,z5,z6]),(0,[z7,z2,z3,z4,z5,z766]),(0,[z7,z2,z342,z3,z4,z114])],[(0,[z7,z2,z767,z3,z4,z6]),(0,[z7,z2,z38,z4,z396,z6]),(0,[z7,z2,z3,z4,z5,z25]),(0,[z7,z43,z61,z3,z4,z117]),(0,[z7,z768,z3,z4,z5,z6])],[(0,[z7,z2,z3,z769,z180,z5]),(0,[z7,z2,z3,z770,z4,z5]),(0,[z7,z2,z3,z4,z771,z6])],[(0,[z690,z2,z3,z4,z9,z6]),(0,[z7,z43,z2,z97,z12,z5])],[(0,[z7,z772,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z773]),(0,[z7,z2,z3,z4,z72,z335]),(0,[z7,z2,z3,z4,z245,z6])],[(0,[z7,z774,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z775,z6]),(0,[z16,z7,z3,z216,z210,z6]),(0,[z16,z7,z381,z3,z216,z6]),(0,[z7,z43,z2,z3,z4,z776]),(0,[z7,z43,z2,z3,z238,z5]),(0,[z7,z43,z2,z3,z5,z587]),(0,[z7,z2,z3,z12,z4,z708])],[(0,[z7,z2,z3,z4,z777,z6]),(0,[z7,z2,z3,z4,z5,z778]),(0,[z7,z43,z2,z779,z4,z5]),(1,[z7,z2,z3,z4,z780])],[(0,[z7,z2,z3,z4,z29,z6]),(0,[z7,z302,z2,z4,z5,z781]),(0,[z7,z782,z2,z3,z4,z6]),(0,[z7,z2,z3,z362,z4,z9]),(0,[z7,z3,z4,z9,z783,z6]),(0,[z7,z784,z167,z2,z3,z5])]],
   [[(0,[z7,z2,z3,z101,z5,z214]),(0,[z7,z43,z2,z338,z3,z4])],[(0,[z7,z2,z3,z4,z9,z785]),(0,[z7,z2,z786,z3,z4,z5])],[(0,[z7,z2,z3,z4,z787,z6]),(0,[z197,z2,z3,z4,z5,z756]),(0,[z7,z2,z4,z788,z5,z6]),(0,[z7,z43,z2,z3,z12,z100])],[(0,[z7,z2,z3,z222,z5,z73]),(0,[z7,z2,z3,z4,z789,z6]),(0,[z7,z2,z3,z4,z790,z6]),(0,[z7,z43,z2,z3,z195,z206])],[],[(0,[z7,z2,z3,z4,z5,z791]),(0,[z7,z2,z3,z792,z5,z6]),(0,[z7,z392,z2,z13,z5,z6]),(0,[z7,z43,z2,z155,z37,z5]),(0,[z7,z2,z793,z4,z5,z6]),(0,[z121,z7,z3,z4,z29,z297]),(0,[z7,z2,z155,z97,z4,z5])],[(0,[z7,z2,z3,z4,z794,z6]),(0,[z7,z2,z3,z4,z29,z523]),(0,[z7,z43,z2,z79,z5,z65])],[],[(0,[z7,z260,z3,z96,z5,z6]),(0,[z7,z2,z3,z4,z5,z795]),(0,[z7,z167,z51,z12,z4,z5])],[(1,[z722,z3,z4,z5,z6]),(0,[z7,z2,z3,z796,z4,z5]),(0,[z7,z2,z3,z4,z797,z6]),(0,[z7,z167,z51,z4,z5,z532]),(0,[z7,z125,z2,z3,z453,z6])],[(0,[z7,z302,z2,z4,z29,z6]),(0,[z7,z2,z3,z4,z5,z798]),(0,[z7,z2,z3,z4,z799,z6])],[(1,[z7,z784,z2,z3,z5]),(0,[z7,z2,z3,z800,z4,z5]),(0,[z7,z2,z3,z4,z5,z801]),(0,[z7,z2,z3,z12,z4,z109]),(0,[z7,z2,z49,z3,z4,z114])],[(0,[z7,z802,z2,z3,z4,z5]),(0,[z1,z722,z3,z4,z5,z6]),(0,[z7,z43,z2,z3,z5,z517])],[(0,[z7,z2,z803,z3,z4,z6])],[(0,[z7,z43,z2,z3,z4,z328]),(0,[z7,z2,z3,z5,z804,z6])],[(0,[z7,z2,z3,z4,z805,z6]),(0,[z7,z2,z155,z4,z29,z6]),(0,[z7,z43,z2,z3,z386,z5]),(0,[z16,z7,z3,z12,z216,z5]),(0,[z7,z2,z3,z362,z4,z383]),(0,[z7,z2,z4,z5,z70,z806])]],
   [[(0,[z7,z2,z97,z4,z9,z6]),(0,[z2,z3,z4,z154,z29,z6]),(0,[z7,z125,z2,z3,z5,z6]),(0,[z7,z2,z4,z5,z806,z65]),(0,[z7,z43,z2,z3,z5,z477]),(0,[z284,z175,z2,z3,z4,z5])],[(0,[z7,z2,z3,z4,z807,z6]),(0,[z7,z2,z3,z4,z808,z6]),(0,[z7,z2,z294,z3,z4,z383]),(0,[z7,z2,z3,z4,z809,z6])],[(0,[z7,z2,z3,z4,z5,z810]),(0,[z7,z2,z3,z811,z5,z6]),(0,[z7,z2,z3,z812,z5,z6]),(0,[z7,z43,z392,z2,z3,z5]),(0,[z7,z2,z3,z12,z222,z5]),(0,[z7,z2,z152,z3,z144,z4])],[(0,[z7,z2,z3,z4,z9,z6]),(0,[z7,z43,z2,z3,z4,z463]),(0,[z197,z10,z2,z3,z4,z5]),(0,[z7,z43,z2,z3,z132,z5])],[(0,[z7,z2,z3,z4,z813,z6]),(0,[z7,z2,z3,z4,z814,z6]),(0,[z7,z2,z3,z4,z815,z6])],[(0,[z7,z341,z3,z4,z29,z6]),(0,[z7,z2,z816,z3,z4,z25]),(0,[z7,z2,z3,z144,z4,z5])],[(0,[z7,z2,z152,z3,z4,z6]),(0,[z7,z2,z79,z5,z6,z539]),(0,[z7,z2,z3,z817,z5,z6]),(0,[z7,z43,z2,z818,z97,z4])],[(0,[z7,z819,z2,z3,z101,z5]),(0,[z7,z2,z3,z4,z820,z6]),(0,[z2,z3,z821,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z822]),(0,[z2,z3,z99,z4,z9,z6]),(0,[z7,z2,z3,z4,z823,z6]),(0,[z7,z43,z595,z2,z3,z5]),(0,[z7,z3,z4,z5,z763,z6]),(0,[z7,z824,z2,z3,z4,z5]),(0,[z7,z43,z825,z3,z4,z5])],[(0,[z7,z2,z3,z180,z5,z424]),(0,[z7,z18,z2,z3,z66,z6])],[(1,[z2,z3,z4,z826,z6]),(0,[z505,z2,z3,z4,z29,z6]),(0,[z7,z2,z827,z3,z4,z6]),(0,[z7,z2,z3,z4,z5,z157]),(0,[z7,z93,z2,z230,z13,z5])],[(0,[z7,z43,z2,z97,z37,z5]),(0,[z7,z2,z3,z4,z9,z523]),(0,[z7,z312,z2,z4,z20,z6])],[],[(0,[z7,z2,z3,z828,z5,z6]),(0,[z7,z2,z3,z359,z4,z829]),(0,[z7,z2,z3,z4,z9,z830]),(0,[z7,z2,z3,z12,z4,z831]),(0,[z7,z832,z2,z3,z4,z5])],[(0,[z7,z2,z3,z4,z833,z6]),(0,[z7,z43,z432,z2,z3,z5]),(0,[z7,z2,z3,z12,z4,z834])],[(0,[z7,z2,z3,z362,z4,z29]),(0,[z7,z2,z835,z3,z4,z6])],[(0,[z7,z836,z2,z3,z4,z6]),(0,[z7,z2,z3,z5,z41,z561])]],
   [[(0,[z7,z2,z3,z4,z5,z837]),(0,[z7,z2,z3,z4,z838,z6])],[(0,[z7,z2,z3,z839,z278,z5]),(0,[z611,z2,z3,z37,z5,z6]),(0,[z7,z2,z3,z4,z840,z6]),(0,[z7,z43,z93,z2,z13,z5])],[(0,[z7,z67,z637,z4,z5,z6]),(0,[z7,z167,z341,z4,z5,z6]),(0,[z7,z2,z3,z222,z5,z60])],[(0,[z7,z2,z155,z4,z9,z6]),(0,[z7,z2,z3,z4,z182,z6]),(0,[z205,z2,z3,z4,z29,z6]),(0,[z7,z447,z43,z2,z3,z5]),(0,[z7,z2,z3,z12,z5,z243])],[(0,[z7,z2,z3,z4,z841,z6]),(0,[z7,z2,z3,z4,z842,z6]),(0,[z30,z2,z173,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z785]),(0,[z7,z2,z3,z4,z5,z843]),(0,[z7,z2,z3,z844,z4,z5]),(0,[z7,z394,z2,z49,z3,z5])],[(0,[z7,z43,z2,z3,z71,z5]),(0,[z7,z2,z3,z12,z431,z5]),(0,[z7,z43,z2,z3,z376,z5])],[(0,[z7,z43,z2,z3,z180,z5]),(0,[z156,z2,z3,z4,z9,z6]),(0,[z7,z125,z2,z3,z5,z73]),(0,[z7,z43,z2,z3,z365,z5])],[(0,[z7,z2,z3,z4,z5,z845]),(0,[z7,z2,z3,z846,z4,z5]),(0,[z7,z43,z2,z3,z232,z5]),(0,[z7,z2,z19,z4,z21,z6]),(0,[z7,z2,z3,z5,z847,z6])],[(0,[z7,z848,z2,z3,z5,z6]),(0,[z7,z2,z3,z71,z5,z6])],[(0,[z7,z2,z3,z4,z849,z6]),(0,[z7,z341,z3,z4,z9,z6]),(0,[z7,z2,z3,z359,z5,z41]),(0,[z7,z850,z3,z4,z5,z6]),(0,[z7,z2,z155,z4,z5,z157]),(0,[z7,z2,z3,z4,z100,z109])],[(0,[z7,z2,z3,z4,z5,z851])],[(0,[z7,z2,z3,z4,z852,z6]),(0,[z7,z2,z3,z12,z4,z100]),(0,[z7,z43,z2,z3,z202,z5])],[(0,[z107,z2,z3,z325,z5,z60]),(0,[z7,z141,z3,z5,z221,z6]),(0,[z7,z394,z2,z3,z5,z6]),(0,[z7,z2,z3,z4,z6,z853]),(0,[z7,z63,z2,z4,z5,z806]),(0,[z7,z43,z2,z49,z3,z66])],[(0,[z7,z3,z4,z854,z5,z6]),(0,[z7,z2,z3,z4,z213,z6]),(0,[z7,z43,z2,z3,z5,z389])],[(0,[z7,z43,z2,z3,z278,z5]),(0,[z7,z2,z3,z4,z5,z855]),(0,[z7,z784,z2,z3,z4,z5]),(0,[z16,z7,z43,z168,z3,z5]),(0,[z7,z43,z856,z3,z4,z5]),(0,[z7,z2,z3,z402,z14,z6])],[(0,[z7,z2,z857,z3,z4,z6]),(0,[z7,z2,z3,z4,z233,z109])]],
   [[(0,[z1,z33,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z9,z858]),(0,[z7,z2,z3,z9,z859,z6]),(0,[z121,z7,z3,z4,z172,z5])],[(0,[z7,z2,z3,z860,z101,z5]),(0,[z7,z2,z3,z4,z861,z6]),(0,[z7,z2,z3,z4,z210,z6]),(1,[z7,z824,z2,z3,z5]),(0,[z7,z43,z2,z3,z697,z5]),(0,[z7,z43,z2,z862,z4,z5])],[(0,[z7,z2,z3,z4,z863,z6]),(0,[z7,z2,z3,z4,z491,z214]),(0,[z7,z2,z3,z4,z5,z864]),(0,[z7,z865,z2,z3,z4,z5]),(0,[z866,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z867,z4,z5]),(0,[z7,z394,z2,z3,z5,z297]),(0,[z7,z2,z79,z240,z5,z6])],[(0,[z7,z2,z3,z4,z868,z6]),(0,[z2,z3,z4,z242,z29,z6]),(0,[z7,z2,z3,z412,z206,z6]),(0,[z7,z2,z3,z4,z869,z6]),(0,[z7,z3,z4,z5,z297,z763]),(0,[z7,z426,z2,z97,z4,z5])],[(0,[z7,z2,z403,z4,z140,z6])],[(0,[z7,z870,z2,z3,z4,z5])],[(0,[z7,z2,z88,z4,z5,z214]),(0,[z7,z871,z2,z3,z71,z5]),(0,[z7,z2,z3,z4,z834,z6]),(0,[z7,z141,z3,z96,z5,z6]),(0,[z7,z223,z3,z4,z117,z6])],[(0,[z7,z2,z3,z4,z5,z872]),(0,[z7,z2,z3,z873,z4,z5])],[(0,[z7,z302,z341,z4,z5,z6]),(0,[z146,z2,z110,z4,z29,z6])],[(0,[z7,z2,z3,z4,z9,z331]),(0,[z7,z874,z2,z4,z5,z6]),(0,[z7,z2,z875,z4,z9,z6]),(0,[z7,z43,z2,z3,z4,z429]),(0,[z7,z2,z97,z4,z5,z297]),(0,[z7,z43,z2,z3,z4,z876]),(0,[z7,z43,z877,z2,z3,z4])],[(0,[z7,z2,z3,z4,z878,z6]),(0,[z7,z2,z3,z102,z402,z14])],[(0,[z0,z83,z3,z278,z5,z6]),(0,[z7,z2,z3,z4,z5,z879]),(0,[z7,z43,z2,z880,z4,z5])],[(0,[z7,z2,z3,z5,z26,z137])],[(0,[z164,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z29,z243,z6]),(0,[z7,z43,z2,z19,z3,z195])],[(0,[z7,z341,z3,z71,z5,z6]),(0,[z2,z3,z4,z29,z9,z6]),(0,[z153,z2,z3,z4,z9,z6]),(0,[z7,z43,z2,z3,z4,z182]),(0,[z7,z43,z125,z2,z3,z5]),(0,[z7,z2,z3,z4,z881,z6]),(0,[z7,z2,z3,z4,z5,z882]),(0,[z7,z2,z3,z12,z195,z206]),(0,[z7,z43,z2,z3,z4,z729])],[(0,[z7,z2,z3,z4,z5,z830]),(0,[z7,z758,z51,z4,z5,z6]),(0,[z7,z883,z2,z3,z4,z6])]],
   [[(0,[z7,z884,z2,z3,z4,z5]),(0,[z7,z133,z2,z4,z20,z6]),(0,[z7,z2,z3,z195,z201,z6])],[(0,[z7,z141,z2,z885,z3,z5])],[(0,[z7,z3,z886,z216,z5,z6]),(0,[z7,z43,z2,z3,z5,z270])],[(0,[z7,z2,z747,z3,z4,z137]),(0,[z7,z43,z103,z2,z3,z5]),(0,[z7,z18,z43,z2,z3,z66])],[(0,[z7,z43,z2,z3,z101,z5]),(0,[z7,z2,z294,z3,z4,z9]),(0,[z2,z3,z4,z9,z6,z357])],[(0,[z7,z2,z3,z887,z4,z5]),(0,[z7,z43,z2,z3,z4,z209]),(0,[z7,z888,z2,z3,z5,z6]),(0,[z7,z125,z2,z3,z5,z60]),(0,[z16,z7,z3,z216,z5,z6]),(0,[z7,z43,z2,z889,z4,z5])],[(0,[z113,z2,z3,z238,z4,z5])],[(0,[z7,z2,z890,z4,z5,z6]),(0,[z7,z2,z3,z891,z5,z6]),(0,[z7,z63,z43,z2,z79,z5]),(0,[z7,z892,z2,z3,z4,z5])],[(0,[z7,z2,z3,z4,z395,z214])],[(0,[z7,z2,z87,z4,z5,z6]),(0,[z7,z43,z2,z3,z5,z116])],[(0,[z7,z2,z3,z4,z5,z893]),(0,[z7,z394,z2,z64,z3,z5]),(0,[z7,z2,z3,z4,z5,z894])],[(0,[z326,z2,z3,z105,z5,z6]),(0,[z7,z2,z19,z703,z4,z6])],[(0,[z146,z2,z110,z4,z9,z6]),(0,[z7,z895,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z896]),(0,[z7,z2,z3,z4,z5,z897])],[(0,[z7,z2,z3,z4,z898,z6]),(0,[z7,z2,z3,z4,z102,z780])],[(0,[z0,z83,z3,z4,z491,z6]),(0,[z7,z2,z899,z3,z4,z6]),(0,[z2,z3,z4,z490,z29,z6]),(0,[z7,z2,z3,z12,z5,z545]),(0,[z7,z2,z3,z12,z132,z5])],[(0,[z7,z2,z3,z222,z415,z6]),(0,[z7,z2,z3,z4,z5,z900]),(0,[z7,z2,z3,z150,z206,z6]),(0,[z7,z394,z2,z3,z5,z27]),(0,[z7,z2,z901,z3,z4,z5])]],
   [[(0,[z7,z902,z3,z4,z29,z6]),(0,[z7,z2,z155,z4,z5,z70]),(0,[z7,z2,z3,z12,z4,z903])],[],[(0,[z7,z2,z3,z12,z4,z904])],[(0,[z7,z2,z905,z4,z5,z6]),(0,[z7,z2,z3,z9,z26,z6])],[(0,[z7,z2,z3,z906,z5,z6]),(0,[z7,z907,z2,z3,z4,z5]),(0,[z7,z2,z49,z3,z4,z569]),(0,[z7,z133,z2,z12,z4,z20]),(0,[z7,z394,z2,z3,z241,z6])],[(0,[z7,z2,z3,z71,z209,z6])],[(0,[z7,z2,z3,z4,z29,z135]),(0,[z7,z2,z3,z4,z5,z908]),(0,[z7,z2,z97,z4,z5,z27])],[(0,[z7,z2,z3,z4,z29,z137]),(0,[z7,z2,z3,z4,z5,z909]),(0,[z7,z2,z3,z229,z66,z6])],[(0,[z347,z2,z3,z4,z29,z6])],[(0,[z1,z33,z3,z4,z128,z6]),(0,[z7,z167,z51,z4,z5,z25]),(0,[z7,z2,z4,z910,z5,z6]),(0,[z7,z2,z230,z97,z4,z5])],[(0,[z7,z2,z3,z4,z911,z6])],[(0,[z2,z355,z3,z4,z29,z6]),(0,[z7,z2,z3,z4,z912,z6])],[(0,[z7,z2,z3,z4,z5,z331]),(0,[z121,z7,z3,z4,z9,z297]),(0,[z107,z2,z3,z222,z5,z60]),(0,[z16,z7,z43,z371,z3,z5])],[(0,[z7,z2,z3,z12,z277,z5])],[(0,[z913,z2,z3,z4,z5,z6]),(0,[z7,z825,z3,z4,z5,z6]),(0,[z7,z856,z3,z4,z5,z6]),(0,[z7,z2,z3,z12,z5,z402])],[(0,[z0,z83,z3,z101,z5,z6]),(0,[z7,z2,z3,z4,z411,z6]),(0,[z7,z167,z51,z4,z29,z6]),(0,[z16,z7,z43,z2,z3,z29]),(0,[z385,z7,z3,z4,z5,z297]),(0,[z7,z2,z3,z5,z914,z6]),(0,[z7,z2,z3,z4,z5,z763]),(0,[z7,z63,z2,z230,z4,z5]),(0,[z7,z2,z3,z5,z737,z6]),(0,[z7,z2,z3,z5,z233,z402]),(0,[z7,z877,z2,z97,z4,z6])]],
   [[],[(0,[z7,z302,z2,z4,z9,z6]),(0,[z146,z2,z110,z71,z5,z6]),(0,[z7,z2,z3,z12,z180,z5]),(0,[z7,z2,z3,z4,z9,z915]),(0,[z7,z43,z2,z3,z29,z66]),(0,[z7,z394,z2,z3,z5,z60]),(0,[z7,z437,z43,z2,z3,z5]),(0,[z16,z7,z3,z383,z216,z6]),(0,[z7,z2,z3,z4,z916,z6])],[(0,[z7,z2,z917,z4,z5,z6]),(0,[z7,z2,z3,z362,z4,z5])],[(0,[z7,z2,z4,z5,z918,z6]),(0,[z15,z2,z3,z4,z9,z6]),(0,[z7,z2,z294,z3,z4,z29]),(0,[z7,z2,z3,z12,z4,z415]),(0,[z7,z2,z3,z5,z919,z25]),(0,[z7,z2,z3,z5,z6,z920])],[(0,[z0,z83,z3,z4,z395,z6]),(0,[z7,z249,z3,z4,z5,z424]),(0,[z7,z2,z3,z4,z921,z6]),(0,[z7,z43,z2,z3,z4,z72]),(0,[z7,z2,z294,z3,z4,z5])],[(0,[z7,z43,z2,z3,z560,z5]),(0,[z7,z449,z2,z97,z4,z5])],[(0,[z7,z2,z3,z4,z5,z922]),(0,[z7,z2,z3,z180,z29,z6])],[(0,[z7,z2,z3,z4,z923,z6]),(0,[z7,z2,z924,z3,z4,z6]),(0,[z7,z485,z3,z4,z5,z297]),(0,[z7,z2,z3,z4,z925,z6]),(0,[z7,z2,z3,z12,z4,z926])],[(0,[z7,z83,z87,z4,z5,z6]),(0,[z7,z50,z2,z4,z286,z6]),(0,[z7,z2,z3,z4,z927,z6]),(0,[z7,z2,z3,z12,z612,z5])],[(0,[z7,z2,z3,z12,z278,z5]),(0,[z7,z341,z173,z4,z5,z6]),(0,[z7,z2,z3,z4,z429,z6]),(0,[z7,z43,z2,z3,z29,z148]),(0,[z7,z2,z122,z3,z4,z212]),(0,[z522,z2,z3,z4,z29,z6])],[(0,[z626,z2,z3,z4,z9,z6]),(0,[z7,z784,z2,z3,z5,z25]),(0,[z7,z91,z444,z3,z4,z27]),(0,[z7,z2,z3,z928,z5,z6])],[(0,[z7,z2,z3,z4,z9,z137]),(0,[z544,z2,z3,z4,z5,z73]),(0,[z7,z43,z929,z2,z3,z4])],[(0,[z7,z2,z3,z4,z930,z6]),(0,[z7,z2,z3,z4,z383,z6]),(0,[z7,z2,z3,z4,z931,z6]),(0,[z7,z2,z3,z4,z932,z561])],[(0,[z7,z2,z3,z933,z5,z6]),(0,[z7,z43,z2,z3,z4,z314])],[(0,[z7,z2,z3,z4,z934,z6]),(0,[z107,z2,z3,z4,z29,z60]),(0,[z7,z43,z2,z3,z4,z548]),(0,[z7,z43,z141,z3,z96,z5]),(0,[z7,z2,z3,z5,z935,z24])],[(0,[z7,z2,z87,z4,z5,z331]),(0,[z7,z2,z936,z4,z5,z6]),(0,[z7,z937,z2,z3,z4,z6]),(0,[z7,z2,z64,z5,z243,z65]),(0,[z7,z2,z168,z97,z4,z5])]],
   [[(0,[z7,z43,z2,z3,z672,z5]),(0,[z7,z43,z2,z155,z5,z24])],[(0,[z7,z2,z3,z4,z29,z214]),(0,[z7,z2,z3,z4,z938,z6]),(0,[z7,z2,z3,z202,z206,z6]),(0,[z7,z43,z2,z176,z3,z5])],[(0,[z7,z2,z3,z4,z453,z6]),(0,[z7,z2,z3,z4,z5,z939])],[(0,[z7,z2,z3,z4,z940,z6]),(0,[z7,z167,z51,z4,z9,z6]),(0,[z7,z2,z3,z4,z311,z14]),(0,[z7,z2,z3,z4,z5,z941]),(0,[z7,z2,z942,z3,z4,z6])],[(0,[z7,z2,z3,z132,z29,z6])],[(0,[z7,z2,z3,z4,z943,z6]),(0,[z2,z3,z4,z9,z481,z6]),(0,[z7,z43,z2,z3,z9,z66]),(0,[z7,z2,z3,z4,z14,z523])],[(0,[z7,z2,z97,z4,z5,z6])],[(0,[z7,z43,z302,z2,z4,z5]),(0,[z7,z483,z31,z4,z5,z6]),(0,[z7,z682,z51,z4,z5,z6]),(0,[z7,z2,z885,z3,z4,z5]),(0,[z7,z125,z2,z3,z5,z65])],[(0,[z7,z2,z3,z4,z944,z6]),(0,[z698,z7,z43,z2,z3,z5]),(0,[z7,z67,z758,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6]),(0,[z0,z83,z3,z12,z4,z5]),(0,[z7,z2,z3,z4,z5,z945]),(0,[z147,z2,z3,z743,z5,z6]),(0,[z7,z2,z3,z12,z4,z182]),(0,[z497,z2,z3,z4,z5,z60]),(0,[z7,z43,z2,z3,z5,z520])],[(0,[z7,z2,z3,z180,z9,z6]),(0,[z7,z43,z2,z571,z3,z5]),(0,[z7,z2,z3,z4,z29,z233]),(0,[z7,z142,z3,z4,z55,z6])],[(0,[z7,z2,z946,z4,z5,z6]),(0,[z7,z947,z3,z4,z5,z6]),(0,[z7,z2,z3,z886,z5,z6])],[(0,[z7,z2,z3,z5,z948,z6]),(0,[z7,z2,z3,z4,z422,z6]),(0,[z7,z43,z423,z2,z3,z5]),(0,[z7,z43,z2,z3,z109,z6])],[(0,[z7,z2,z3,z949,z5,z6]),(0,[z7,z2,z3,z4,z5,z950])],[(0,[z0,z722,z3,z4,z5,z6]),(0,[z7,z951,z2,z4,z5,z6]),(0,[z7,z2,z3,z952,z5,z6]),(0,[z7,z2,z3,z4,z5,z953]),(0,[z7,z2,z3,z5,z847,z135]),(0,[z7,z43,z2,z3,z309,z5])],[(0,[z7,z2,z3,z12,z101,z5]),(0,[z7,z2,z3,z4,z954,z6]),(0,[z7,z43,z589,z2,z3,z5]),(0,[z7,z2,z3,z955,z4,z5]),(0,[z7,z2,z3,z4,z5,z956])]],
   [[(0,[z7,z2,z3,z4,z957,z6]),(0,[z7,z2,z3,z29,z26,z6]),(0,[z7,z2,z3,z4,z5,z523])],[(0,[z7,z2,z3,z4,z5,z958]),(0,[z7,z2,z294,z3,z105,z5]),(0,[z7,z43,z2,z3,z5,z137])],[(0,[z107,z2,z3,z4,z9,z60]),(0,[z7,z2,z3,z4,z959,z25]),(0,[z7,z43,z895,z3,z4,z5])],[(0,[z1,z33,z3,z4,z118,z6]),(0,[z7,z249,z3,z4,z5,z335]),(0,[z98,z2,z3,z743,z5,z6]),(0,[z16,z7,z43,z2,z3,z9]),(0,[z7,z2,z3,z4,z960,z6]),(0,[z7,z43,z2,z3,z334,z5])],[(0,[z7,z381,z2,z3,z12,z4])],[(0,[z7,z2,z3,z4,z9,z214]),(0,[z7,z2,z3,z961,z5,z6]),(0,[z7,z43,z2,z3,z687,z5]),(0,[z138,z2,z3,z4,z29,z6]),(0,[z7,z394,z2,z3,z5,z73]),(0,[z7,z43,z2,z97,z5,z24])],[(0,[z7,z43,z2,z3,z9,z77]),(0,[z7,z2,z3,z4,z962,z6])],[(0,[z7,z2,z3,z4,z963,z6]),(0,[z7,z43,z2,z3,z435,z5]),(0,[z7,z2,z3,z4,z964,z6]),(0,[z7,z43,z67,z31,z4,z5]),(0,[z7,z2,z3,z195,z5,z458])],[(0,[z7,z2,z3,z132,z9,z6]),(0,[z7,z2,z3,z4,z5,z965]),(0,[z966,z2,z3,z4,z5,z6]),(0,[z7,z43,z2,z35,z3,z5]),(0,[z7,z43,z967,z3,z4,z5])],[(0,[z7,z2,z3,z968,z4,z5]),(0,[z7,z2,z3,z359,z4,z9]),(0,[z7,z2,z3,z4,z969,z6]),(0,[z7,z2,z3,z4,z970,z6]),(0,[z7,z2,z155,z4,z5,z6])],[(0,[z7,z2,z3,z4,z971,z6]),(0,[z7,z2,z3,z4,z972,z6]),(0,[z7,z61,z692,z3,z4,z6]),(0,[z7,z43,z2,z3,z55,z66]),(0,[z7,z2,z3,z4,z973,z6]),(1,[z7,z2,z3,z5,z935]),(0,[z7,z43,z2,z3,z5,z935]),(0,[z7,z2,z3,z12,z4,z974])],[],[(0,[z146,z2,z821,z4,z5,z6]),(0,[z7,z2,z3,z12,z4,z328]),(0,[z7,z2,z97,z4,z5,z73]),(0,[z576,z7,z2,z155,z4,z5])],[(0,[z0,z83,z3,z4,z29,z6]),(0,[z602,z7,z43,z2,z3,z5]),(0,[z7,z2,z3,z4,z975,z6])],[(0,[z7,z43,z2,z3,z305,z5]),(0,[z7,z2,z3,z4,z9,z233]),(0,[z7,z2,z3,z976,z4,z5]),(0,[z7,z141,z3,z96,z5,z137]),(0,[z7,z2,z49,z3,z4,z523])],[(0,[z7,z341,z3,z4,z5,z6]),(0,[z7,z133,z2,z4,z618,z6])]],
   [[(0,[z348,z2,z3,z37,z5,z6]),(0,[z2,z3,z4,z9,z538,z6]),(0,[z7,z2,z19,z4,z669,z6])],[(0,[z7,z2,z3,z4,z977,z6]),(0,[z7,z2,z3,z12,z4,z463]),(0,[z147,z2,z3,z359,z37,z5]),(0,[z284,z2,z3,z4,z5,z60]),(0,[z7,z2,z3,z4,z978,z6]),(0,[z7,z3,z4,z717,z117,z6])],[(0,[z7,z2,z3,z4,z979,z6]),(0,[z7,z2,z3,z101,z491,z6]),(0,[z7,z980,z2,z3,z4,z5]),(0,[z7,z2,z3,z981,z5,z6]),(0,[z107,z2,z3,z4,z182,z60]),(0,[z7,z2,z49,z3,z4,z241])],[(0,[z7,z2,z3,z52,z41,z6])],[(0,[z7,z2,z3,z982,z5,z6]),(0,[z16,z7,z43,z2,z3,z52]),(0,[z7,z2,z3,z983,z5,z6]),(0,[z7,z43,z2,z79,z240,z5])],[(0,[z0,z83,z88,z4,z5,z6]),(0,[z0,z43,z83,z3,z4,z5]),(0,[z7,z2,z294,z3,z37,z5]),(0,[z7,z2,z816,z3,z4,z6]),(0,[z7,z2,z3,z4,z5,z984])],[(0,[z7,z2,z3,z4,z5,z858]),(0,[z7,z2,z3,z4,z5,z985]),(0,[z7,z394,z2,z338,z3,z6]),(0,[z7,z2,z3,z5,z402,z6])],[(0,[z7,z2,z3,z71,z72,z6]),(0,[z701,z2,z3,z37,z5,z6]),(0,[z7,z2,z3,z4,z986,z6]),(0,[z7,z2,z3,z4,z987,z6]),(0,[z7,z133,z2,z4,z20,z135]),(0,[z7,z2,z988,z3,z4,z6])],[(0,[z7,z2,z3,z4,z989,z6]),(0,[z7,z2,z3,z4,z829,z6]),(0,[z7,z43,z133,z2,z4,z20])],[(0,[z7,z67,z302,z4,z5,z6]),(0,[z7,z2,z3,z4,z990,z6]),(0,[z7,z43,z2,z3,z66,z14])],[(0,[z7,z43,z2,z3,z398,z5]),(0,[z7,z2,z991,z3,z4,z5]),(0,[z7,z43,z141,z2,z3,z9]),(0,[z7,z2,z3,z195,z310,z6]),(0,[z7,z43,z2,z3,z106,z5])],[(0,[z7,z2,z3,z4,z5,z992]),(0,[z7,z500,z51,z4,z5,z6]),(0,[z7,z2,z993,z3,z4,z5]),(0,[z7,z2,z3,z4,z994,z6]),(1,[z7,z2,z4,z5,z806])],[(0,[z7,z2,z3,z4,z5,z995]),(0,[z58,z43,z2,z3,z4,z9]),(0,[z7,z67,z31,z12,z4,z5]),(0,[z7,z2,z3,z5,z243,z561]),(0,[z7,z2,z240,z910,z5,z6])],[(0,[z2,z3,z105,z743,z5,z6]),(0,[z7,z2,z3,z453,z26,z6])],[(0,[z7,z249,z3,z12,z4,z5]),(0,[z7,z2,z3,z359,z325,z5]),(0,[z7,z996,z3,z4,z9,z6]),(0,[z7,z43,z2,z3,z80,z5]),(0,[z7,z43,z2,z3,z4,z210]),(0,[z7,z2,z3,z12,z165,z5])],[(0,[z7,z2,z3,z12,z4,z72]),(0,[z7,z2,z3,z4,z5,z997]),(0,[z7,z2,z875,z4,z5,z6]),(0,[z7,z2,z3,z4,z123,z6]),(0,[z7,z2,z998,z4,z5,z6]),(0,[z7,z2,z64,z97,z4,z5]),(0,[z7,z43,z999,z2,z3,z4])]],
   [[(0,[z7,z43,z2,z3,z4,z123]),(0,[z7,z2,z3,z376,z4,z100])],[(0,[z7,z125,z91,z2,z3,z5]),(0,[z7,z2,z3,z4,z903,z6]),(0,[z7,z43,z2,z3,z4,z115]),(0,[z7,z2,z3,z4,z241,z6]),(0,[z1000,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z128,z6]),(0,[z7,z2,z1001,z4,z5,z6]),(0,[z121,z7,z3,z4,z5,z763]),(0,[z7,z2,z338,z3,z243,z6]),(0,[z7,z2,z3,z737,z66,z6]),(0,[z7,z2,z3,z132,z5,z14])],[(0,[z7,z2,z3,z12,z71,z5]),(0,[z7,z43,z2,z3,z549,z5]),(0,[z16,z7,z43,z2,z3,z5]),(0,[z7,z61,z3,z640,z4,z6]),(0,[z7,z2,z338,z64,z4,z65])],[(0,[z7,z2,z3,z4,z5,z1002]),(0,[z7,z125,z91,z3,z5,z27]),(0,[z7,z43,z2,z3,z5,z233])],[(0,[z15,z83,z3,z4,z5,z6])],[(0,[z7,z1003,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z209,z6]),(0,[z7,z2,z3,z4,z5,z1004]),(0,[z2,z3,z4,z5,z6,z1005]),(0,[z7,z63,z394,z2,z3,z5]),(0,[z7,z2,z3,z12,z4,z1006])],[(0,[z7,z1007,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z5,z1008]),(0,[z7,z2,z3,z4,z1009,z6]),(0,[z7,z2,z3,z4,z5,z806]),(0,[z7,z2,z176,z496,z4,z5])],[(0,[z7,z2,z3,z101,z395,z6]),(0,[z7,z2,z3,z359,z4,z29]),(0,[z7,z2,z3,z12,z4,z314])],[(0,[z7,z1010,z2,z3,z4,z6]),(0,[z7,z2,z3,z1011,z4,z5])],[(0,[z7,z2,z3,z1012,z4,z5]),(0,[z7,z691,z3,z4,z55,z6]),(0,[z7,z2,z3,z4,z5,z1013])],[(0,[z7,z2,z3,z29,z1014,z6]),(0,[z7,z2,z295,z3,z4,z29]),(0,[z7,z2,z97,z4,z5,z60]),(0,[z7,z2,z3,z4,z1015,z5])],[(0,[z7,z1016,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z876,z6])],[(0,[z7,z2,z1017,z3,z4,z6]),(0,[z2,z3,z4,z826,z9,z6]),(0,[z7,z2,z3,z4,z9,z135]),(0,[z550,z2,z3,z4,z29,z6]),(0,[z287,z10,z2,z3,z4,z5])],[(0,[z7,z2,z3,z12,z29,z41])],[(0,[z7,z2,z3,z1018,z71,z5])]],
   [[(0,[z11,z2,z3,z4,z5,z73]),(0,[z7,z43,z142,z2,z3,z195])],[(0,[z7,z2,z3,z278,z491,z6]),(0,[z7,z43,z2,z3,z195,z9]),(0,[z7,z2,z3,z66,z536,z6])],[(0,[z146,z2,z110,z4,z5,z6]),(0,[z7,z249,z3,z4,z29,z6]),(0,[z7,z67,z438,z4,z5,z6])],[(0,[z7,z2,z3,z4,z1019,z6]),(0,[z7,z2,z3,z4,z29,z1020]),(0,[z7,z1021,z2,z3,z4,z5])],[(0,[z7,z43,z2,z515,z3,z5])],[(0,[z7,z2,z88,z278,z5,z6]),(0,[z441,z2,z173,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1022]),(0,[z7,z131,z3,z4,z5,z27]),(0,[z7,z2,z3,z4,z6,z1023]),(0,[z7,z43,z2,z3,z526,z5]),(0,[z7,z2,z3,z132,z5,z70]),(0,[z677,z7,z168,z3,z4,z5]),(0,[z7,z2,z3,z132,z5,z114])],[(0,[z7,z2,z3,z1024,z4,z5]),(0,[z7,z2,z1025,z3,z4,z6])],[(0,[z664,z7,z43,z2,z3,z5]),(0,[z7,z2,z3,z12,z4,z429]),(0,[z7,z2,z3,z4,z788,z6]),(0,[z7,z2,z818,z3,z4,z6])],[(0,[z7,z43,z249,z3,z4,z5]),(0,[z7,z2,z3,z1026,z5,z6]),(0,[z7,z43,z2,z3,z479,z5])],[(0,[z7,z43,z141,z2,z3,z29]),(0,[z40,z7,z2,z3,z66,z6]),(0,[z1027,z43,z2,z3,z4,z5])],[(0,[z7,z43,z141,z2,z3,z5])],[(0,[z7,z2,z87,z4,z5,z214]),(0,[z7,z2,z1028,z3,z4,z5]),(0,[z7,z2,z3,z4,z1029,z6]),(0,[z7,z2,z3,z4,z1030,z6]),(0,[z7,z2,z3,z1031,z5,z6])],[(0,[z7,z2,z1032,z3,z4,z5]),(0,[z7,z341,z3,z4,z209,z6]),(0,[z7,z43,z2,z3,z195,z262])],[(0,[z7,z18,z2,z3,z12,z66])],[(0,[z7,z208,z3,z4,z404,z6]),(0,[z7,z2,z3,z4,z29,z1033]),(0,[z7,z417,z43,z2,z3,z5])],[]],
   [[(0,[z7,z2,z3,z5,z1034,z6]),(0,[z7,z257,z2,z3,z4,z109])],[(0,[z317,z33,z3,z4,z5,z6]),(0,[z7,z43,z260,z2,z3,z5]),(0,[z7,z43,z2,z3,z5,z52])],[(0,[z7,z2,z3,z12,z9,z41]),(0,[z7,z381,z2,z3,z4,z6]),(0,[z121,z7,z3,z4,z5,z297])],[(0,[z7,z2,z3,z12,z4,z209])],[(0,[z147,z2,z3,z37,z29,z6]),(0,[z510,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z756]),(0,[z7,z43,z2,z3,z264,z5])],[(0,[z7,z2,z3,z1035,z5,z6]),(0,[z7,z2,z3,z4,z14,z135]),(0,[z7,z43,z2,z3,z4,z840]),(0,[z7,z2,z3,z12,z5,z935])],[(0,[z7,z2,z3,z4,z1036,z6]),(0,[z7,z2,z49,z3,z4,z212])],[(0,[z7,z2,z3,z278,z395,z6]),(0,[z7,z302,z2,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z915]),(0,[z7,z2,z49,z3,z402,z6])],[(0,[z146,z341,z110,z4,z5,z6]),(0,[z2,z3,z570,z4,z9,z6]),(0,[z36,z2,z3,z4,z5,z60]),(0,[z7,z2,z3,z4,z314,z6]),(0,[z7,z2,z3,z4,z1037,z6]),(0,[z7,z2,z1038,z3,z4,z6]),(0,[z7,z2,z3,z4,z5,z1039]),(0,[z7,z43,z2,z3,z5,z695])],[(0,[z7,z2,z342,z3,z4,z267]),(0,[z16,z7,z3,z362,z216,z5]),(0,[z7,z43,z93,z2,z79,z5]),(0,[z7,z2,z3,z12,z4,z1040]),(0,[z7,z2,z3,z4,z102,z14])],[(0,[z7,z2,z3,z5,z1041,z6]),(0,[z43,z2,z3,z4,z29,z9]),(0,[z7,z2,z3,z4,z776,z6]),(0,[z7,z2,z3,z4,z5,z1042]),(0,[z7,z2,z408,z4,z5,z65])],[(0,[z7,z2,z3,z4,z1043,z6]),(0,[z7,z43,z2,z3,z336,z9]),(0,[z7,z2,z3,z4,z1044,z6]),(0,[z7,z2,z3,z4,z1045,z6]),(0,[z716,z43,z2,z3,z4,z5]),(0,[z7,z43,z2,z3,z5,z471])],[(0,[z7,z2,z3,z4,z118,z6]),(0,[z7,z1046,z2,z4,z5,z6]),(0,[z7,z2,z1047,z3,z4,z29]),(0,[z7,z2,z3,z4,z5,z1048]),(0,[z7,z142,z3,z4,z514,z6]),(0,[z7,z2,z3,z4,z109,z6])],[(0,[z7,z43,z2,z3,z412,z29]),(0,[z7,z2,z1047,z3,z4,z5]),(0,[z7,z141,z3,z12,z96,z5]),(0,[z7,z2,z1049,z3,z4,z6]),(0,[z7,z43,z131,z2,z3,z5])],[(0,[z7,z1050,z3,z4,z5,z6]),(0,[z7,z43,z2,z3,z412,z5]),(0,[z7,z675,z2,z4,z5,z70]),(0,[z7,z2,z3,z4,z1051,z6])],[(0,[z7,z2,z295,z3,z4,z9]),(0,[z7,z2,z3,z4,z5,z1052]),(0,[z7,z43,z133,z2,z3,z195]),(1,[z7,z2,z3,z737,z6])]],
   [[(0,[z7,z43,z2,z3,z195,z29]),(0,[z706,z7,z43,z2,z3,z5]),(0,[z7,z2,z3,z4,z5,z135]),(0,[z7,z43,z2,z3,z4,z1053])],[(0,[z7,z2,z3,z101,z29,z6]),(0,[z7,z2,z3,z4,z5,z137]),(0,[z7,z43,z2,z3,z4,z241]),(0,[z7,z43,z2,z3,z195,z5])],[(0,[z7,z2,z4,z5,z1054,z6]),(0,[z7,z2,z3,z4,z5,z1055]),(0,[z7,z2,z4,z9,z918,z6]),(0,[z7,z2,z3,z4,z1056,z6])],[(0,[z7,z43,z2,z3,z4,z118]),(0,[z2,z3,z4,z9,z695,z6]),(0,[z7,z2,z3,z1057,z5,z6]),(0,[z7,z824,z2,z3,z5,z6]),(0,[z7,z2,z3,z4,z1058,z6]),(0,[z7,z2,z3,z4,z100,z14])],[],[],[(0,[z7,z2,z3,z4,z1059,z6]),(0,[z7,z43,z2,z3,z5,z495]),(0,[z7,z2,z49,z3,z4,z262])],[(0,[z7,z2,z1060,z4,z5,z6]),(0,[z7,z1061,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z1062,z6])],[(0,[z147,z2,z3,z37,z9,z6])],[(0,[z7,z2,z88,z101,z5,z6]),(0,[z7,z167,z51,z4,z5,z6]),(0,[z7,z2,z3,z12,z4,z210]),(1,[z7,z3,z4,z717,z6]),(0,[z7,z158,z2,z4,z5,z70]),(0,[z7,z2,z3,z4,z233,z14])],[(0,[z7,z2,z3,z1063,z5,z6]),(0,[z7,z2,z3,z1064,z4,z5]),(0,[z7,z43,z247,z2,z3,z5]),(0,[z7,z2,z3,z4,z5,z935]),(0,[z7,z2,z3,z4,z281,z100])],[(0,[z7,z1065,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z415,z6]),(0,[z7,z43,z2,z3,z5,z66])],[(0,[z7,z1066,z2,z3,z5,z6]),(0,[z7,z2,z1067,z4,z9,z6]),(0,[z7,z2,z3,z4,z737,z6]),(0,[z7,z43,z2,z3,z195,z66]),(0,[z7,z447,z43,z2,z155,z5])],[(0,[z7,z2,z3,z4,z5,z1068])],[(0,[z7,z2,z3,z4,z1069,z6]),(0,[z7,z43,z341,z3,z4,z5]),(0,[z7,z43,z2,z3,z4,z422]),(0,[z98,z2,z3,z105,z5,z134]),(0,[z7,z43,z2,z3,z95,z5]),(0,[z7,z2,z49,z3,z4,z135])],[(0,[z7,z2,z3,z359,z4,z762])]],
   [[(0,[z7,z2,z3,z180,z5,z6]),(0,[z7,z2,z3,z1070,z4,z5]),(0,[z2,z3,z4,z5,z60,z756]),(0,[z7,z2,z1071,z3,z4,z6]),(0,[z354,z7,z125,z2,z3,z5]),(0,[z7,z2,z3,z4,z5,z1072]),(0,[z7,z2,z4,z20,z788,z6]),(0,[z7,z43,z877,z2,z97,z4])],[(0,[z7,z2,z3,z4,z5,z1073]),(0,[z7,z2,z3,z4,z5,z1074]),(0,[z7,z2,z3,z4,z1075,z6]),(0,[z7,z417,z2,z3,z66,z6])],[(0,[z7,z43,z2,z1076,z4,z5])],[(0,[z7,z91,z168,z3,z4,z5]),(0,[z7,z133,z2,z4,z647,z6])],[(0,[z0,z83,z3,z4,z9,z6]),(0,[z7,z22,z2,z4,z1077,z6]),(0,[z7,z2,z3,z4,z5,z1078]),(0,[z7,z2,z3,z1079,z9,z6]),(0,[z7,z43,z61,z2,z3,z195]),(0,[z40,z7,z43,z2,z3,z66])],[(0,[z7,z22,z2,z12,z4,z5]),(0,[z7,z2,z444,z3,z26,z6]),(0,[z7,z2,z3,z4,z1080,z6])],[(0,[z7,z2,z3,z4,z100,z70]),(0,[z7,z2,z3,z195,z206,z6]),(0,[z7,z2,z3,z4,z100,z114])],[(0,[z7,z2,z3,z1024,z37,z5]),(0,[z284,z43,z2,z3,z105,z5]),(0,[z7,z2,z1081,z4,z5,z6]),(0,[z7,z43,z108,z2,z3,z5])],[(0,[z7,z2,z3,z4,z72,z6]),(0,[z2,z821,z110,z4,z5,z6]),(0,[z58,z2,z3,z4,z826,z6]),(0,[z2,z3,z12,z4,z29,z9]),(0,[z107,z2,z3,z4,z5,z60]),(0,[z7,z2,z1082,z4,z5,z6]),(0,[z7,z2,z3,z4,z1083,z6])],[(0,[z7,z2,z4,z788,z21,z6]),(0,[z7,z43,z2,z19,z4,z21]),(0,[z40,z7,z2,z3,z4,z262])],[(0,[z30,z662,z2,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z214]),(0,[z7,z865,z2,z3,z180,z5]),(0,[z7,z2,z1084,z3,z4,z6]),(0,[z7,z43,z2,z3,z336,z5]),(0,[z7,z394,z2,z97,z5,z6]),(0,[z7,z2,z3,z4,z201,z14])],[(0,[z7,z2,z3,z359,z4,z5]),(0,[z7,z43,z2,z3,z5,z77]),(0,[z7,z43,z2,z3,z5,z542]),(0,[z7,z2,z3,z4,z29,z532]),(0,[z7,z2,z3,z12,z4,z548]),(0,[z7,z175,z2,z97,z4,z5])],[(0,[z7,z2,z3,z4,z1085,z6]),(0,[z284,z43,z2,z3,z4,z9]),(0,[z7,z2,z3,z12,z4,z740])],[(0,[z7,z2,z910,z13,z5,z6]),(0,[z7,z2,z3,z4,z5,z1086]),(1,[z7,z2,z4,z788,z6]),(0,[z7,z2,z3,z132,z5,z6])],[(0,[z7,z302,z51,z4,z5,z6]),(0,[z2,z3,z4,z702,z29,z6]),(0,[z7,z2,z295,z3,z4,z5])]],
   [[(0,[z7,z2,z3,z278,z29,z6]),(0,[z7,z2,z155,z4,z5,z65]),(0,[z7,z43,z2,z3,z5,z109])],[(0,[z7,z2,z1087,z3,z4,z9]),(0,[z197,z2,z3,z4,z548,z73]),(0,[z7,z2,z315,z4,z5,z65])],[(0,[z7,z353,z3,z4,z5,z27]),(0,[z7,z93,z2,z97,z5,z6])],[(0,[z7,z2,z88,z12,z4,z5]),(0,[z7,z2,z3,z4,z5,z1088]),(0,[z7,z67,z31,z4,z29,z6]),(0,[z7,z2,z3,z4,z1089,z6]),(0,[z7,z2,z3,z1090,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1091]),(0,[z7,z2,z3,z4,z29,z424]),(0,[z704,z2,z3,z4,z9,z6]),(0,[z7,z2,z79,z97,z5,z6]),(0,[z7,z2,z3,z4,z5,z233])],[],[(0,[z7,z341,z3,z180,z5,z6]),(0,[z7,z2,z3,z5,z1092,z6]),(0,[z7,z2,z1093,z3,z4,z6]),(0,[z7,z3,z4,z55,z717,z6]),(0,[z7,z2,z3,z1094,z5,z6])],[(0,[z7,z1095,z2,z3,z4,z6]),(0,[z2,z173,z821,z4,z5,z6]),(0,[z7,z2,z3,z4,z1096,z6]),(0,[z7,z2,z3,z1097,z4,z5]),(0,[z7,z2,z3,z4,z5,z1098]),(0,[z7,z91,z3,z5,z26,z27]),(0,[z7,z574,z2,z4,z5,z70]),(0,[z7,z2,z3,z4,z1099,z6])],[(0,[z7,z2,z3,z4,z1006,z6]),(0,[z98,z2,z3,z105,z245,z6]),(0,[z682,z2,z3,z4,z9,z6]),(0,[z7,z43,z93,z2,z3,z9])],[(0,[z7,z1100,z2,z3,z5,z6]),(0,[z30,z2,z821,z4,z5,z6])],[(0,[z7,z2,z1101,z4,z9,z6]),(0,[z7,z2,z3,z4,z29,z561]),(0,[z7,z2,z3,z4,z5,z1102])],[(0,[z98,z2,z3,z105,z29,z6]),(0,[z7,z43,z2,z79,z3,z9]),(0,[z7,z2,z3,z4,z1103,z6]),(0,[z7,z2,z3,z4,z5,z1104]),(0,[z7,z371,z3,z4,z5,z297]),(0,[z7,z43,z2,z3,z5,z288])],[(0,[z7,z2,z3,z4,z1105,z6])],[(0,[z7,z2,z3,z1106,z5,z6]),(0,[z7,z2,z880,z4,z5,z6]),(0,[z7,z2,z3,z4,z29,z1107]),(0,[z7,z18,z2,z3,z233,z66])],[(0,[z7,z2,z3,z4,z5,z1108]),(0,[z7,z341,z3,z4,z72,z6]),(0,[z147,z2,z3,z37,z422,z6]),(0,[z7,z2,z3,z4,z1109,z6])],[(0,[z7,z2,z3,z4,z5,z1110]),(0,[z7,z43,z2,z3,z570,z5])]],
   [[(0,[z7,z2,z3,z325,z29,z6]),(0,[z7,z2,z3,z4,z1111,z6]),(0,[z7,z43,z2,z885,z3,z5])],[(0,[z7,z2,z3,z5,z1112,z6]),(0,[z7,z2,z3,z4,z1113,z6])],[(0,[z7,z2,z3,z4,z1114,z6]),(0,[z7,z2,z49,z3,z4,z233])],[(0,[z7,z2,z3,z4,z5,z1115]),(0,[z7,z2,z862,z4,z5,z6]),(0,[z7,z43,z2,z3,z105,z29]),(0,[z7,z2,z3,z1116,z5,z6])],[(0,[z7,z2,z3,z278,z9,z6]),(0,[z7,z2,z3,z4,z1117,z6]),(0,[z7,z2,z3,z1118,z5,z6]),(0,[z7,z996,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z29,z458]),(0,[z7,z43,z2,z3,z5,z604])],[(0,[z7,z2,z3,z743,z5,z6]),(0,[z10,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z9,z402,z6]),(0,[z7,z2,z3,z4,z1119,z6]),(0,[z7,z2,z3,z4,z5,z1120]),(0,[z7,z2,z3,z4,z1121,z6])],[(0,[z7,z2,z3,z4,z5,z1122]),(0,[z7,z2,z3,z4,z5,z1123]),(0,[z7,z2,z3,z4,z5,z1124]),(0,[z7,z43,z2,z793,z4,z5]),(0,[z7,z2,z3,z376,z132,z5])],[(0,[z7,z67,z31,z4,z9,z6]),(0,[z7,z2,z3,z1079,z5,z6]),(0,[z7,z2,z3,z4,z1125,z6])],[(0,[z7,z43,z2,z298,z3,z5]),(0,[z98,z43,z2,z3,z105,z5]),(0,[z7,z1126,z2,z3,z9,z6])],[(0,[z7,z2,z3,z1127,z5,z6]),(0,[z7,z249,z3,z4,z9,z6]),(0,[z7,z2,z403,z4,z21,z6]),(0,[z7,z2,z3,z12,z4,z1128])],[(0,[z7,z2,z3,z1129,z5,z6]),(0,[z7,z2,z3,z5,z1130,z6]),(0,[z7,z2,z3,z1131,z4,z5]),(0,[z7,z43,z2,z3,z4,z9]),(0,[z7,z2,z3,z4,z1132,z6]),(0,[z7,z2,z3,z4,z6,z780])],[(0,[z7,z2,z88,z4,z491,z6]),(0,[z7,z43,z2,z3,z5,z622])],[(0,[z7,z1133,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z1134,z6]),(0,[z7,z43,z2,z3,z5,z377]),(0,[z7,z2,z3,z4,z5,z1135]),(0,[z7,z2,z3,z12,z4,z241])],[(0,[z7,z902,z3,z4,z5,z6]),(0,[z7,z2,z3,z12,z4,z878]),(0,[z7,z2,z3,z1136,z5,z6]),(0,[z7,z2,z3,z12,z4,z898])],[(0,[z7,z2,z3,z4,z9,z561]),(0,[z16,z7,z294,z3,z216,z5])],[(0,[z98,z2,z3,z105,z9,z6]),(0,[z7,z2,z4,z5,z1137,z6]),(0,[z45,z43,z2,z3,z4,z29]),(0,[z7,z1138,z2,z3,z5,z6])]],
   [[(0,[z7,z1139,z2,z4,z5,z6]),(0,[z7,z142,z3,z4,z8,z6]),(0,[z197,z2,z3,z4,z29,z73]),(0,[z7,z2,z64,z4,z29,z65]),(0,[z7,z141,z3,z886,z5,z6]),(0,[z7,z93,z2,z230,z3,z5]),(0,[z7,z2,z3,z4,z1140,z5])],[(0,[z7,z1141,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z1142,z6]),(0,[z2,z3,z4,z743,z5,z6]),(0,[z7,z2,z1087,z3,z4,z5]),(0,[z7,z43,z2,z1081,z4,z5])],[(0,[z7,z1143,z2,z3,z4,z5]),(0,[z7,z2,z4,z1144,z5,z6]),(0,[z147,z43,z2,z3,z37,z5]),(0,[z7,z91,z3,z4,z29,z27]),(0,[z7,z2,z79,z230,z3,z5]),(0,[z7,z2,z3,z309,z66,z6])],[(0,[z7,z2,z3,z4,z29,z335]),(0,[z2,z3,z4,z826,z5,z6]),(0,[z7,z2,z176,z4,z5,z65])],[(0,[z7,z2,z3,z4,z1145,z6]),(0,[z7,z2,z3,z325,z9,z6]),(0,[z7,z3,z4,z886,z5,z6])],[(0,[z7,z43,z2,z3,z4,z395]),(0,[z7,z142,z3,z4,z658,z6]),(0,[z7,z43,z394,z2,z3,z5]),(0,[z7,z2,z1146,z4,z5,z6])],[(0,[z7,z3,z4,z5,z1147,z6])],[(0,[z7,z22,z2,z4,z718,z6]),(0,[z7,z43,z93,z2,z3,z29]),(0,[z7,z2,z3,z1148,z4,z5])],[(0,[z7,z1149,z3,z4,z5,z6]),(0,[z98,z2,z3,z105,z5,z166]),(0,[z7,z2,z3,z4,z9,z458]),(0,[z7,z43,z93,z2,z3,z5])],[(0,[z7,z2,z1150,z4,z5,z6]),(0,[z7,z2,z3,z1151,z29,z6]),(0,[z7,z2,z3,z4,z1152,z6]),(0,[z7,z43,z2,z3,z150,z5]),(0,[z7,z2,z444,z3,z12,z4]),(0,[z7,z2,z338,z3,z12,z4])],[(0,[z0,z83,z87,z4,z5,z6]),(0,[z58,z2,z3,z12,z4,z9]),(0,[z7,z43,z2,z79,z3,z29]),(0,[z7,z43,z2,z3,z4,z383]),(0,[z7,z2,z3,z4,z5,z1153])],[(0,[z16,z7,z168,z3,z5,z6]),(0,[z7,z43,z2,z79,z3,z5])],[(0,[z7,z2,z3,z4,z1154,z6]),(0,[z7,z299,z3,z4,z8,z6]),(0,[z7,z43,z2,z3,z12,z9]),(0,[z594,z2,z3,z4,z29,z6]),(0,[z7,z2,z152,z230,z3,z4]),(0,[z7,z2,z3,z5,z1155,z6])],[(0,[z7,z2,z3,z4,z9,z1156]),(0,[z7,z2,z3,z4,z1157,z6]),(0,[z7,z2,z3,z1158,z5,z6])],[(0,[z7,z249,z3,z71,z5,z6]),(0,[z7,z2,z3,z12,z4,z123]),(0,[z1159,z2,z3,z4,z5,z6]),(0,[z7,z2,z444,z3,z4,z70])],[(0,[z7,z43,z2,z3,z325,z5]),(0,[z7,z2,z3,z12,z4,z115]),(0,[z7,z2,z3,z4,z100,z6])]],
   [[(0,[z7,z2,z1160,z4,z5,z6]),(0,[z7,z2,z3,z4,z102,z241])],[(0,[z7,z2,z88,z4,z395,z6]),(0,[z0,z22,z83,z4,z5,z6]),(0,[z7,z2,z3,z4,z1161,z6]),(0,[z146,z2,z110,z4,z72,z6]),(0,[z7,z419,z2,z3,z77,z6])],[(0,[z146,z2,z110,z4,z209,z6]),(0,[z7,z2,z3,z4,z245,z134]),(0,[z7,z2,z3,z336,z310,z6])],[(0,[z7,z2,z1162,z3,z4,z6]),(0,[z7,z125,z2,z3,z12,z5]),(0,[z7,z2,z1163,z3,z4,z5])],[(0,[z7,z2,z1164,z4,z5,z6]),(0,[z147,z2,z3,z37,z411,z6]),(0,[z7,z2,z64,z4,z9,z65]),(0,[z7,z2,z3,z325,z182,z6]),(0,[z7,z43,z2,z3,z5,z561])],[(0,[z7,z2,z3,z4,z5,z1165]),(0,[z7,z2,z3,z4,z29,z134]),(0,[z7,z43,z2,z3,z373,z5])],[(0,[z7,z2,z1166,z3,z4,z6]),(0,[z7,z91,z3,z4,z9,z27]),(0,[z7,z2,z3,z4,z1167,z6]),(0,[z7,z43,z2,z3,z5,z148]),(0,[z7,z2,z3,z5,z919,z6]),(0,[z7,z447,z2,z4,z281,z5])],[(0,[z7,z2,z3,z4,z9,z335]),(0,[z7,z2,z3,z4,z1168,z6]),(0,[z7,z43,z2,z3,z105,z9]),(0,[z7,z2,z3,z4,z29,z1169]),(0,[z7,z2,z3,z1170,z5,z6]),(0,[z7,z133,z2,z4,z788,z6])],[(0,[z7,z2,z3,z101,z9,z6]),(0,[z7,z2,z821,z4,z5,z6]),(0,[z7,z2,z3,z4,z1171,z6]),(0,[z7,z61,z3,z12,z4,z117]),(0,[z7,z2,z3,z4,z5,z1172]),(0,[z7,z2,z3,z12,z5,z41])],[(0,[z7,z2,z3,z4,z1173,z6]),(0,[z98,z2,z3,z105,z213,z6]),(0,[z7,z43,z2,z3,z4,z29]),(0,[z107,z2,z3,z238,z4,z5])],[(0,[z7,z1174,z3,z4,z5,z6]),(0,[z7,z2,z3,z37,z5,z166]),(0,[z16,z7,z3,z886,z5,z6]),(0,[z7,z2,z3,z4,z1175,z6]),(0,[z7,z93,z2,z12,z13,z5]),(0,[z7,z824,z2,z3,z5,z135])],[],[],[(0,[z0,z83,z3,z4,z5,z331]),(0,[z7,z2,z3,z4,z5,z1020]),(0,[z7,z43,z2,z3,z291,z5]),(0,[z7,z784,z2,z3,z5,z6]),(0,[z121,z7,z125,z2,z3,z5]),(0,[z7,z93,z2,z115,z13,z6])],[(0,[z7,z2,z4,z5,z1176,z6]),(0,[z7,z1177,z2,z3,z5,z6])],[(0,[z7,z2,z3,z12,z5,z410])]],
   [[(0,[z7,z2,z49,z3,z4,z487]),(1,[z7,z2,z910,z5,z6]),(0,[z7,z43,z2,z1163,z3,z5]),(0,[z7,z2,z3,z195,z206,z523]),(0,[z7,z131,z3,z217,z4,z5])],[(0,[z7,z43,z2,z3,z359,z5]),(0,[z7,z43,z2,z3,z5,z683]),(0,[z7,z999,z2,z3,z4,z6])],[(0,[z7,z2,z4,z5,z1178,z6]),(0,[z7,z2,z3,z29,z402,z6])],[(0,[z7,z43,z22,z2,z4,z5]),(0,[z7,z43,z381,z2,z3,z4]),(0,[z7,z43,z2,z3,z320,z5]),(0,[z7,z43,z2,z3,z5,z461])],[(0,[z7,z2,z3,z1179,z4,z5]),(0,[z7,z2,z3,z4,z1180,z6]),(0,[z7,z758,z3,z4,z5,z6])],[(0,[z7,z93,z2,z152,z13,z6]),(0,[z7,z394,z2,z64,z5,z65])],[(0,[z7,z2,z3,z1181,z4,z5]),(0,[z7,z2,z3,z4,z5,z1182]),(0,[z7,z2,z3,z4,z1183,z6])],[],[(0,[z7,z2,z3,z4,z5,z1033]),(0,[z231,z2,z3,z4,z29,z6]),(1,[z7,z758,z4,z5,z6]),(0,[z7,z43,z2,z443,z3,z5])],[(0,[z7,z2,z3,z4,z9,z134]),(0,[z7,z167,z758,z4,z5,z6]),(1,[z7,z43,z2,z3,z52])],[(0,[z7,z2,z87,z278,z5,z6]),(0,[z30,z2,z173,z4,z328,z6]),(0,[z7,z2,z3,z496,z4,z100])],[(0,[z7,z871,z2,z3,z4,z5]),(0,[z7,z43,z2,z3,z37,z9]),(0,[z7,z43,z2,z3,z4,z213]),(0,[z7,z43,z2,z3,z12,z29]),(0,[z7,z2,z3,z4,z241,z135])],[(0,[z7,z22,z2,z4,z29,z6]),(0,[z7,z2,z3,z71,z5,z335]),(0,[z7,z43,z2,z3,z4,z411]),(0,[z7,z2,z3,z4,z29,z25]),(0,[z7,z2,z3,z4,z5,z1184]),(0,[z130,z7,z43,z2,z3,z5]),(0,[z7,z2,z3,z910,z5,z6]),(0,[z7,z2,z79,z1163,z3,z5]),(0,[z7,z43,z2,z3,z12,z5])],[(0,[z7,z2,z3,z4,z5,z1185]),(0,[z7,z2,z3,z4,z29,z32]),(0,[z7,z43,z2,z3,z195,z201]),(0,[z11,z2,z3,z251,z4,z5])],[(0,[z7,z2,z3,z4,z5,z1186]),(0,[z7,z43,z2,z3,z4,z128]),(0,[z147,z2,z3,z37,z5,z6]),(0,[z7,z824,z133,z2,z3,z5]),(0,[z7,z2,z3,z132,z102,z14])],[(0,[z2,z722,z3,z4,z5,z6]),(0,[z7,z43,z2,z204,z3,z5])]],
   [[(0,[z7,z819,z2,z3,z4,z5])],[(0,[z7,z2,z3,z769,z4,z5]),(0,[z107,z2,z3,z4,z5,z756])],[(0,[z7,z2,z1067,z4,z5,z6])],[(0,[z98,z2,z3,z12,z105,z5]),(0,[z7,z2,z3,z4,z9,z532]),(0,[z7,z2,z3,z4,z1187,z6]),(0,[z7,z43,z2,z1188,z4,z5])],[(0,[z7,z43,z2,z3,z529,z5]),(1,[z2,z3,z4,z5,z756]),(0,[z7,z2,z3,z4,z1189,z6]),(0,[z7,z381,z2,z3,z362,z4]),(0,[z7,z2,z230,z4,z5,z65])],[(0,[z7,z2,z3,z4,z959,z6]),(0,[z7,z43,z2,z3,z5,z26]),(0,[z7,z2,z3,z4,z1190,z6])],[(0,[z7,z1191,z2,z3,z5,z6])],[(0,[z7,z2,z3,z1192,z5,z6]),(0,[z7,z2,z3,z1193,z5,z6]),(0,[z7,z2,z3,z4,z1194,z6]),(0,[z7,z43,z2,z3,z105,z5]),(0,[z7,z2,z3,z4,z1195,z6])],[],[(0,[z7,z967,z3,z4,z5,z6]),(0,[z578,z2,z3,z4,z29,z6]),(0,[z7,z2,z3,z144,z4,z115])],[(0,[z0,z83,z3,z4,z5,z6]),(0,[z7,z2,z88,z4,z29,z6]),(0,[z7,z93,z2,z13,z29,z6]),(0,[z107,z2,z3,z4,z415,z60]),(0,[z16,z7,z43,z2,z97,z5]),(0,[z7,z43,z223,z2,z3,z5])],[(0,[z7,z2,z3,z4,z9,z424]),(0,[z7,z2,z3,z4,z1196,z9]),(0,[z7,z63,z2,z4,z29,z70]),(0,[z7,z2,z19,z12,z4,z21]),(0,[z7,z43,z2,z719,z4,z5])],[(0,[z7,z2,z3,z4,z5,z1197]),(0,[z7,z2,z3,z4,z1198,z6]),(0,[z7,z43,z2,z3,z29,z24])],[(0,[z147,z2,z3,z12,z37,z5]),(0,[z7,z2,z1199,z3,z4,z6]),(0,[z7,z2,z3,z1200,z5,z6])],[(0,[z86,z2,z3,z4,z9,z6]),(0,[z7,z2,z49,z3,z4,z109])],[(0,[z7,z2,z3,z180,z72,z6]),(0,[z30,z2,z173,z4,z463,z6])]],
   [[(0,[z7,z22,z2,z4,z9,z6]),(0,[z7,z2,z3,z180,z209,z6]),(0,[z7,z2,z3,z4,z1053,z6]),(0,[z7,z2,z1188,z4,z5,z6]),(0,[z7,z2,z3,z1201,z5,z6]),(0,[z7,z2,z3,z4,z1202,z6])],[(0,[z7,z2,z3,z12,z4,z118]),(0,[z7,z2,z3,z4,z9,z32]),(0,[z7,z2,z4,z1203,z9,z6]),(0,[z7,z218,z43,z2,z3,z5]),(0,[z7,z2,z3,z1204,z5,z6]),(0,[z7,z2,z64,z4,z5,z806])],[(0,[z7,z1205,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z1206,z6]),(0,[z7,z2,z3,z4,z5,z1207]),(0,[z7,z2,z3,z4,z904,z6]),(0,[z1000,z43,z2,z3,z4,z5])],[(0,[z30,z2,z173,z12,z4,z5]),(0,[z7,z2,z3,z4,z213,z134]),(0,[z7,z125,z2,z3,z29,z6]),(0,[z7,z2,z3,z1208,z5,z6]),(0,[z7,z2,z3,z4,z5,z1209]),(0,[z7,z524,z43,z2,z3,z66])],[(0,[z7,z43,z167,z51,z4,z5]),(0,[z7,z93,z2,z144,z13,z5]),(0,[z7,z2,z230,z3,z4,z115]),(0,[z7,z2,z1210,z4,z5,z6])],[(0,[z7,z2,z3,z12,z4,z383]),(0,[z7,z2,z3,z4,z1211,z6]),(0,[z7,z2,z3,z132,z5,z65])],[(0,[z7,z2,z3,z4,z5,z1212])],[(0,[z7,z2,z3,z105,z5,z166]),(0,[z7,z2,z3,z4,z5,z1213]),(0,[z7,z2,z444,z3,z4,z6]),(0,[z7,z2,z338,z3,z4,z6])],[(0,[z7,z2,z3,z4,z1214,z6]),(0,[z7,z2,z3,z4,z1215,z6])],[(0,[z7,z2,z3,z4,z764,z6])],[(0,[z7,z2,z3,z860,z4,z5]),(0,[z7,z43,z2,z3,z37,z29])],[(0,[z7,z43,z2,z3,z37,z5]),(0,[z7,z43,z2,z444,z3,z4])],[(0,[z146,z2,z110,z180,z5,z6]),(0,[z146,z43,z2,z110,z4,z5]),(0,[z7,z2,z3,z12,z4,z422]),(0,[z7,z2,z3,z4,z245,z166]),(0,[z7,z2,z3,z4,z29,z157]),(0,[z16,z7,z43,z2,z155,z5]),(0,[z7,z2,z3,z109,z41,z6])],[],[(0,[z7,z2,z87,z101,z5,z6]),(0,[z7,z2,z88,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z1216]),(0,[z7,z93,z2,z13,z9,z6]),(0,[z7,z43,z2,z3,z4,z52]),(0,[z7,z3,z4,z5,z717,z6]),(0,[z7,z2,z3,z5,z243,z6]),(0,[z7,z43,z2,z3,z628,z5])],[(0,[z7,z2,z3,z4,z5,z1217]),(0,[z1,z33,z3,z12,z4,z5]),(0,[z7,z2,z3,z4,z29,z166]),(0,[z7,z63,z2,z4,z9,z70]),(0,[z7,z2,z3,z1218,z5,z6]),(0,[z7,z61,z3,z4,z717,z6]),(0,[z7,z200,z3,z4,z55,z6])]],
   [[(0,[z7,z2,z3,z839,z4,z5]),(0,[z7,z2,z3,z71,z5,z424]),(0,[z7,z2,z1101,z4,z5,z6]),(0,[z7,z43,z2,z3,z9,z24])],[(0,[z7,z67,z341,z4,z5,z6]),(0,[z147,z186,z2,z3,z37,z5]),(0,[z7,z266,z3,z4,z117,z6]),(0,[z7,z43,z141,z2,z97,z5])],[(0,[z7,z2,z3,z4,z1219,z6]),(0,[z1220,z2,z3,z4,z5,z6]),(0,[z7,z43,z2,z1210,z4,z5])],[],[(0,[z7,z2,z3,z4,z1221,z6]),(0,[z7,z341,z110,z4,z5,z6]),(0,[z7,z2,z3,z4,z311,z330])],[(0,[z7,z43,z142,z3,z4,z55]),(0,[z7,z43,z162,z2,z3,z5])],[(0,[z7,z2,z3,z4,z5,z1222]),(0,[z7,z2,z3,z4,z29,z730]),(0,[z7,z43,z2,z3,z5,z207])],[(0,[z7,z1003,z2,z3,z278,z5]),(0,[z197,z2,z3,z4,z9,z73]),(0,[z7,z1223,z2,z3,z4,z5])],[(0,[z7,z2,z3,z206,z737,z6]),(1,[z7,z43,z2,z3,z109])],[(0,[z7,z43,z2,z3,z5,z681]),(0,[z7,z2,z3,z4,z100,z523])],[(0,[z7,z2,z3,z278,z5,z6]),(0,[z430,z2,z3,z4,z5,z73])],[(0,[z7,z2,z3,z4,z1196,z5]),(0,[z1,z43,z33,z3,z4,z5]),(0,[z7,z133,z2,z4,z286,z6]),(0,[z7,z2,z3,z4,z1224,z6]),(0,[z7,z2,z3,z1225,z4,z5])],[(0,[z7,z43,z2,z439,z3,z5]),(0,[z7,z2,z1226,z3,z4,z6]),(0,[z7,z2,z3,z5,z233,z41])],[(0,[z7,z43,z2,z3,z4,z5]),(0,[z43,z2,z3,z105,z37,z5]),(0,[z7,z43,z2,z3,z1024,z5]),(0,[z7,z2,z3,z4,z1227,z6]),(0,[z7,z419,z2,z3,z66,z6]),(0,[z7,z67,z31,z4,z5,z6]),(0,[z7,z61,z3,z4,z117,z6]),(0,[z7,z2,z1228,z3,z4,z5])],[(0,[z7,z1126,z2,z3,z5,z6]),(0,[z7,z2,z3,z1229,z5,z6]),(0,[z7,z1230,z2,z3,z4,z5]),(0,[z7,z43,z2,z3,z4,z453])],[(0,[z7,z249,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1231]),(0,[z7,z2,z3,z195,z502,z6]),(0,[z7,z394,z2,z3,z102,z5]),(0,[z7,z43,z2,z818,z3,z4])]],
   [[(0,[z7,z744,z2,z4,z29,z6]),(0,[z7,z2,z3,z4,z1232,z6]),(0,[z7,z2,z79,z240,z5,z561])],[(0,[z7,z2,z3,z4,z1233,z6]),(0,[z7,z2,z3,z101,z5,z331]),(0,[z7,z2,z3,z4,z1234,z6]),(0,[z7,z43,z552,z2,z3,z5]),(0,[z7,z2,z3,z4,z932,z6]),(0,[z1235,z7,z2,z3,z4,z5])],[(0,[z7,z2,z4,z1236,z5,z6])],[(0,[z7,z2,z3,z4,z1237,z6]),(0,[z7,z2,z3,z4,z9,z166]),(0,[z7,z2,z3,z222,z29,z6]),(0,[z7,z312,z2,z4,z179,z6]),(0,[z7,z43,z141,z2,z155,z5]),(0,[z7,z2,z3,z5,z6,z935])],[(0,[z7,z2,z3,z4,z1238,z6]),(0,[z7,z141,z3,z96,z5,z32]),(0,[z7,z2,z3,z4,z5,z561])],[(0,[z98,z2,z3,z105,z5,z6]),(0,[z7,z43,z2,z3,z4,z245])],[(0,[z7,z2,z818,z97,z4,z6]),(0,[z7,z2,z97,z4,z102,z5])],[(0,[z7,z2,z3,z4,z5,z1239]),(0,[z7,z2,z3,z12,z4,z411]),(0,[z7,z2,z3,z4,z5,z1107])],[(0,[z7,z2,z87,z12,z4,z5]),(0,[z7,z186,z2,z3,z4,z29]),(0,[z7,z2,z3,z4,z1240,z6])],[(0,[z43,z10,z2,z3,z105,z5]),(0,[z7,z2,z3,z9,z1130,z6]),(0,[z7,z141,z3,z96,z29,z6]),(0,[z7,z2,z3,z12,z4,z749])],[(0,[z7,z2,z3,z325,z5,z6]),(0,[z586,z2,z3,z4,z9,z6]),(0,[z7,z3,z4,z757,z29,z6]),(0,[z7,z2,z3,z4,z29,z237]),(0,[z7,z2,z3,z4,z1241,z6]),(0,[z7,z2,z3,z4,z5,z1242]),(0,[z40,z7,z2,z97,z4,z5])],[(0,[z575,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z1243,z6]),(0,[z7,z43,z2,z155,z195,z5]),(0,[z7,z2,z3,z12,z109,z41])],[(0,[z7,z2,z3,z4,z6,z1244]),(0,[z7,z43,z2,z593,z3,z5]),(0,[z7,z2,z3,z5,z41,z137]),(0,[z7,z2,z3,z5,z753,z66])],[(0,[z7,z33,z87,z4,z5,z6]),(0,[z7,z93,z2,z910,z5,z6])],[(0,[z7,z2,z4,z9,z1137,z6]),(0,[z7,z2,z19,z4,z788,z6]),(0,[z7,z2,z3,z4,z5,z458])],[(0,[z43,z10,z2,z3,z4,z9]),(0,[z45,z2,z3,z4,z826,z6]),(0,[z7,z2,z79,z910,z5,z6])]],
   [[(0,[z7,z2,z19,z4,z396,z6]),(0,[z7,z2,z3,z12,z5,z26]),(0,[z7,z2,z3,z4,z1245,z6])],[(0,[z7,z2,z3,z4,z1246,z6]),(0,[z7,z2,z3,z12,z4,z970])],[(0,[z668,z2,z3,z4,z9,z6]),(0,[z7,z516,z2,z3,z148,z6]),(0,[z7,z394,z2,z3,z12,z5])],[(0,[z7,z2,z3,z4,z5,z1156]),(0,[z7,z142,z3,z12,z4,z55]),(0,[z7,z43,z2,z3,z4,z1080]),(0,[z7,z929,z2,z3,z4,z6])],[(0,[z7,z341,z3,z4,z5,z424]),(0,[z7,z1247,z3,z4,z5,z6]),(0,[z7,z1248,z3,z4,z5,z6]),(0,[z7,z2,z97,z37,z5,z6])],[(0,[z7,z2,z3,z4,z1249,z6]),(1,[z2,z3,z743,z5,z6]),(0,[z7,z2,z3,z4,z102,z59]),(0,[z7,z2,z3,z4,z717,z6]),(0,[z7,z91,z3,z4,z453,z27]),(0,[z7,z2,z3,z241,z243,z6]),(0,[z7,z43,z2,z155,z5,z66]),(0,[z7,z2,z3,z5,z41,z935])],[(0,[z7,z2,z3,z4,z1250,z5]),(0,[z7,z2,z3,z4,z100,z65]),(0,[z7,z2,z49,z3,z4,z686])],[(0,[z7,z2,z3,z222,z9,z6]),(0,[z7,z2,z3,z4,z1251,z5])],[(0,[z7,z2,z3,z12,z4,z9]),(0,[z16,z7,z3,z216,z29,z6]),(0,[z427,z2,z3,z4,z29,z6]),(0,[z2,z3,z4,z1252,z5,z6]),(0,[z16,z7,z43,z141,z3,z5]),(0,[z7,z2,z79,z240,z12,z5]),(0,[z7,z2,z79,z277,z5,z6]),(0,[z7,z2,z3,z4,z5,z1253])],[(0,[z7,z722,z3,z4,z5,z6]),(0,[z7,z43,z2,z3,z643,z5])],[(0,[z7,z2,z3,z4,z1254,z6]),(0,[z7,z2,z64,z4,z5,z65]),(0,[z7,z2,z3,z4,z1255,z6])],[(0,[z7,z2,z3,z4,z1256,z6]),(0,[z7,z2,z3,z1257,z4,z5]),(0,[z7,z2,z3,z4,z1258,z6])],[(0,[z7,z302,z2,z4,z5,z1186]),(0,[z7,z91,z3,z4,z5,z27]),(0,[z7,z2,z3,z4,z780,z114])],[(0,[z7,z2,z3,z4,z5,z335]),(0,[z7,z2,z3,z4,z213,z166]),(0,[z45,z2,z3,z12,z4,z29]),(0,[z7,z43,z2,z3,z4,z109])],[(0,[z7,z2,z3,z101,z5,z6]),(0,[z7,z2,z3,z4,z9,z237]),(0,[z7,z381,z2,z294,z3,z4]),(0,[z7,z2,z3,z4,z5,z1259])],[(0,[z7,z2,z3,z4,z328,z6]),(0,[z7,z43,z2,z152,z3,z4]),(0,[z7,z43,z2,z3,z556,z5])]],
   [[(0,[z7,z2,z87,z4,z491,z6]),(0,[z7,z2,z3,z278,z5,z331]),(0,[z7,z2,z3,z4,z1260,z6]),(0,[z7,z3,z4,z5,z783,z6]),(0,[z7,z43,z2,z97,z195,z5]),(0,[z7,z2,z3,z4,z1040,z6])],[],[(0,[z7,z91,z3,z4,z5,z763]),(0,[z7,z125,z2,z444,z3,z6])],[(0,[z7,z2,z3,z12,z4,z395]),(0,[z7,z2,z3,z4,z9,z25]),(0,[z7,z2,z3,z1151,z5,z6]),(0,[z7,z2,z3,z4,z1128,z6])],[(0,[z7,z43,z2,z3,z52,z6]),(0,[z7,z125,z2,z3,z5,z70]),(0,[z7,z2,z3,z4,z5,z1261]),(0,[z7,z2,z3,z4,z974,z6])],[(0,[z7,z308,z3,z4,z55,z6]),(0,[z7,z43,z2,z3,z5,z151]),(0,[z7,z2,z152,z3,z12,z4]),(0,[z7,z43,z459,z2,z3,z5])],[(0,[z7,z61,z3,z4,z404,z6])],[(0,[z598,z7,z3,z216,z5,z6]),(0,[z284,z2,z3,z105,z5,z6]),(0,[z7,z1262,z2,z3,z4,z6]),(0,[z7,z2,z3,z222,z182,z6]),(0,[z7,z303,z2,z3,z12,z5])],[],[(0,[z7,z2,z3,z4,z826,z6]),(0,[z7,z2,z230,z3,z4,z29]),(0,[z7,z2,z3,z1263,z4,z5]),(0,[z7,z2,z3,z12,z4,z1058])],[(0,[z7,z2,z3,z4,z1264,z6]),(0,[z7,z2,z3,z4,z1265,z6]),(0,[z2,z3,z4,z5,z756,z6]),(0,[z7,z2,z3,z4,z1266,z6]),(0,[z7,z43,z2,z97,z5,z66])],[(0,[z7,z2,z1267,z4,z5,z6]),(0,[z7,z2,z3,z1268,z5,z6])],[(0,[z7,z249,z3,z4,z209,z6]),(0,[z7,z186,z2,z3,z4,z9]),(0,[z7,z2,z1269,z3,z4,z6])],[(0,[z7,z2,z3,z4,z1270,z6]),(0,[z7,z2,z3,z4,z548,z6]),(0,[z7,z2,z3,z12,z325,z5])],[(0,[z15,z2,z110,z4,z5,z6]),(0,[z442,z7,z43,z2,z3,z5]),(0,[z7,z63,z2,z4,z5,z157])],[(0,[z7,z2,z1271,z3,z4,z6]),(0,[z7,z2,z3,z4,z5,z134]),(0,[z7,z43,z2,z3,z5,z753]),(0,[z7,z43,z2,z3,z12,z109])]],
   [[(0,[z161,z2,z3,z105,z5,z6]),(0,[z7,z877,z2,z3,z4,z6])],[(0,[z7,z2,z3,z4,z1272,z6]),(0,[z7,z2,z515,z240,z5,z6]),(0,[z7,z2,z3,z4,z5,z1169]),(0,[z7,z2,z758,z4,z5,z6]),(0,[z7,z1273,z2,z3,z4,z5]),(0,[z7,z1274,z2,z3,z5,z6])],[],[(0,[z7,z2,z3,z4,z491,z331]),(0,[z7,z341,z3,z4,z5,z335])],[(0,[z7,z43,z2,z3,z4,z491]),(0,[z7,z2,z3,z4,z463,z6]),(0,[z7,z2,z3,z4,z1275,z6]),(0,[z1276,z2,z3,z4,z5,z6])],[(0,[z58,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z14,z187]),(0,[z7,z2,z97,z12,z4,z5])],[(0,[z7,z2,z87,z4,z395,z6]),(0,[z7,z2,z3,z4,z1277,z6]),(0,[z7,z2,z3,z4,z14,z780])],[(0,[z7,z2,z3,z4,z1077,z6]),(0,[z7,z43,z2,z3,z379,z5]),(0,[z7,z2,z3,z12,z4,z29]),(0,[z354,z7,z43,z2,z3,z5])],[(0,[z7,z2,z3,z12,z4,z5]),(0,[z7,z2,z3,z4,z1278,z6]),(0,[z146,z249,z110,z4,z5,z6]),(1,[z2,z821,z4,z5,z6]),(0,[z1279,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1280])],[(0,[z7,z43,z258,z2,z3,z5]),(0,[z7,z2,z1076,z4,z5,z6]),(0,[z7,z43,z2,z3,z170,z5]),(0,[z7,z2,z3,z4,z5,z532]),(0,[z7,z2,z3,z4,z1281,z6]),(0,[z7,z2,z4,z5,z806,z6])],[(0,[z30,z2,z173,z4,z29,z6]),(0,[z7,z125,z2,z3,z9,z6]),(0,[z7,z2,z49,z97,z4,z5])],[(0,[z7,z1282,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z1283,z6])],[],[],[(0,[z7,z2,z3,z71,z29,z6]),(0,[z7,z2,z3,z4,z1284,z6]),(0,[z7,z2,z3,z4,z1285,z6]),(0,[z7,z2,z727,z4,z5,z6])],[(0,[z7,z2,z3,z4,z1286,z6])]],
   [[(0,[z7,z1287,z2,z3,z4,z6]),(0,[z16,z7,z3,z216,z52,z6]),(0,[z7,z2,z3,z4,z1215,z137])],[(0,[z7,z2,z3,z4,z5,z781]),(0,[z7,z2,z3,z4,z5,z424]),(0,[z7,z2,z97,z105,z5,z6]),(0,[z2,z562,z3,z4,z29,z6]),(0,[z7,z43,z2,z3,z5,z406]),(0,[z7,z2,z942,z3,z4,z561]),(0,[z7,z2,z3,z4,z5,z780])],[(0,[z7,z2,z3,z4,z5,z1288]),(0,[z7,z394,z2,z3,z29,z6]),(0,[z7,z2,z3,z4,z5,z1289]),(0,[z7,z2,z779,z4,z5,z6]),(0,[z7,z2,z3,z4,z926,z6]),(0,[z7,z2,z64,z4,z241,z65]),(0,[z7,z2,z3,z4,z1290,z6])],[(0,[z7,z2,z1291,z4,z5,z6]),(0,[z146,z682,z2,z4,z5,z6]),(0,[z7,z2,z3,z4,z1292,z6]),(0,[z7,z2,z3,z4,z9,z157]),(0,[z7,z2,z3,z5,z6,z1293]),(1,[z7,z3,z4,z5,z763]),(0,[z7,z2,z3,z1294,z4,z5])],[(0,[z7,z2,z3,z1018,z4,z5]),(0,[z7,z266,z3,z4,z273,z6]),(0,[z7,z43,z2,z155,z4,z9])],[],[(0,[z7,z43,z2,z87,z4,z5]),(0,[z7,z22,z2,z4,z5,z6]),(0,[z1,z33,z3,z4,z29,z6]),(0,[z7,z2,z3,z412,z269,z6]),(0,[z7,z2,z3,z4,z1295,z6]),(0,[z7,z2,z3,z12,z4,z1219])],[(0,[z7,z2,z4,z1203,z5,z6]),(0,[z7,z2,z230,z3,z105,z5]),(0,[z7,z2,z3,z4,z5,z32]),(0,[z7,z1296,z2,z3,z4,z5])],[(0,[z7,z2,z79,z240,z29,z6]),(0,[z7,z2,z155,z12,z4,z5])],[(0,[z7,z2,z3,z4,z395,z331]),(0,[z7,z2,z3,z12,z4,z213]),(0,[z7,z2,z97,z4,z29,z6]),(0,[z7,z2,z3,z12,z4,z1167])],[(0,[z7,z2,z3,z4,z1297,z6]),(0,[z7,z2,z3,z4,z209,z335]),(0,[z7,z133,z2,z4,z372,z6])],[(0,[z7,z133,z2,z4,z20,z237])],[(0,[z0,z83,z3,z4,z5,z214]),(0,[z7,z2,z3,z12,z4,z128]),(0,[z7,z186,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z831,z6]),(0,[z1298,z2,z3,z4,z5,z6]),(0,[z7,z67,z31,z4,z314,z6]),(0,[z7,z43,z394,z2,z97,z5])],[(0,[z7,z2,z230,z3,z4,z9]),(0,[z197,z2,z3,z4,z429,z73]),(0,[z7,z394,z2,z13,z5,z6]),(0,[z7,z63,z2,z97,z4,z5]),(0,[z7,z2,z3,z5,z66,z458])],[(0,[z7,z2,z3,z4,z5,z1299]),(0,[z7,z341,z3,z12,z4,z5]),(0,[z7,z2,z3,z1300,z5,z6]),(0,[z30,z2,z173,z4,z9,z6]),(0,[z7,z308,z3,z4,z531,z6]),(0,[z7,z2,z444,z3,z4,z65])],[(0,[z7,z18,z2,z3,z320,z6]),(0,[z7,z43,z93,z2,z97,z5]),(0,[z7,z18,z2,z3,z737,z6]),(0,[z7,z2,z49,z3,z4,z780])]],
   [[(0,[z7,z2,z3,z4,z491,z6])],[(0,[z7,z2,z3,z4,z1301,z6]),(0,[z7,z2,z3,z5,z859,z6])],[(0,[z33,z722,z3,z4,z5,z6]),(0,[z7,z2,z3,z71,z9,z6]),(0,[z2,z3,z4,z1302,z5,z6]),(0,[z16,z7,z43,z3,z216,z5]),(0,[z7,z2,z3,z4,z1303,z6]),(0,[z7,z43,z2,z79,z97,z5])],[(0,[z7,z43,z2,z97,z105,z5]),(0,[z7,z2,z3,z1304,z4,z5]),(0,[z7,z2,z3,z4,z5,z1305])],[(0,[z7,z2,z88,z4,z5,z6]),(0,[z7,z2,z3,z4,z1306,z6]),(0,[z7,z2,z3,z846,z4,z9]),(0,[z2,z3,z4,z29,z826,z6]),(0,[z7,z93,z2,z13,z5,z6])],[(0,[z7,z2,z889,z4,z5,z6]),(0,[z7,z63,z2,z4,z5,z70]),(0,[z1027,z2,z3,z4,z5,z6]),(0,[z7,z18,z2,z295,z3,z66])],[(0,[z7,z1307,z3,z4,z5,z6]),(0,[z146,z2,z110,z4,z5,z335]),(0,[z7,z394,z2,z3,z9,z6]),(0,[z7,z2,z3,z4,z5,z1308]),(0,[z7,z639,z3,z4,z5,z27]),(0,[z7,z43,z2,z3,z5,z24]),(0,[z7,z2,z3,z12,z4,z1099])],[(0,[z7,z2,z3,z1309,z5,z6]),(0,[z7,z2,z3,z4,z5,z1310])],[(0,[z7,z3,z96,z886,z5,z6]),(0,[z7,z43,z2,z1146,z4,z5])],[(0,[z7,z43,z2,z97,z4,z9]),(0,[z7,z2,z3,z251,z222,z5]),(0,[z7,z2,z1311,z4,z5,z6])],[(0,[z1,z33,z3,z4,z9,z6]),(0,[z7,z2,z4,z29,z1176,z6]),(0,[z7,z2,z3,z4,z1312,z6]),(0,[z7,z141,z2,z294,z3,z5]),(0,[z7,z2,z3,z4,z115,z6]),(0,[z7,z2,z1313,z3,z4,z5])],[(0,[z7,z2,z230,z3,z37,z5])],[(0,[z7,z2,z3,z4,z5,z1314]),(0,[z7,z2,z79,z240,z9,z6]),(0,[z7,z2,z3,z5,z1014,z6])],[(0,[z7,z2,z3,z4,z5,z1315]),(0,[z7,z2,z3,z9,z243,z6]),(0,[z197,z2,z3,z4,z5,z73]),(0,[z7,z43,z2,z46,z3,z5]),(0,[z7,z2,z614,z4,z5,z65])],[(0,[z7,z2,z3,z195,z685,z6]),(0,[z7,z2,z3,z12,z100,z41])],[(0,[z7,z2,z87,z4,z29,z6]),(0,[z7,z2,z3,z4,z1316,z6]),(0,[z7,z358,z51,z4,z5,z6]),(1,[z7,z3,z886,z5,z6]),(0,[z7,z2,z3,z4,z6,z1317]),(0,[z1159,z43,z2,z3,z4,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 495) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 495).take 500) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 995).take 419) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1414)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [495, 500, 419] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 143).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 143).take 133).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 276).take 130).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 406).take 106).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [143, 133, 130, 106] = true :=
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

end PEqualNP.Outside.L_meta_38861

theorem PEqualNP.Outside.L_meta_38861 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4209680544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4209680544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38861.solve