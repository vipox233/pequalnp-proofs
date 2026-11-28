import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38653

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
  Nat.testBit (4276808384 * 2 ^ 32 + 4006144704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0000d62b84318ae5#64 ++ 0x40001ac57086315c#64 ++ 0x9809fe7f8c739fe7#64 ++ 0xb3013fcff18e73fc#64 : BitVec 256),
   (0x00323098a186a629#64 ++ 0x800646131430d4c5#64 ++ 0xb8763199f39fe67f#64 ++ 0x770ec6333e73fccf#64 : BitVec 256),
   (0x0b85c1615c185856#64 ++ 0x0170b82c2b830b0a#64 ++ 0xef87c1e1fc1c787e#64 ++ 0xfdf0f83c3f838f0f#64 : BitVec 256),
   (0x15d801d41ac07500#64 ++ 0x02bb003a83580ea0#64 ++ 0xfff801fe1fe07f85#64 ++ 0xffff003fc3fc0ff0#64 : BitVec 256),
   (0x26ef6a001f7f0000#64 ++ 0x04dded4003efe000#64 ++ 0xf7fffe001fff8003#64 ++ 0xfeffffc003fff000#64 : BitVec 256),
   (0x477fbdffe0000000#64 ++ 0x08eff7bffc000000#64 ++ 0x47ffffffe0000007#64 ++ 0xe8fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [8, 4]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [10, 2]⟩, ⟨.and, [9, 5]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [7, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000942b80008ae5 0x400012857000115c 0x0800007f80001fe4 0x0100000ff00003fc

def z1 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x9809fe7f8c739fe7 0xb3013fcff18e73fc

def z2 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0xb8763199f39fe67f 0x770ec6333e73fccf

def z3 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0xef87c1e1fc1c787e 0xfdf0f83c3f838f0f

def z4 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0xfff801fe1fe07f85 0xffff003fc3fc0ff0

def z5 : W := mkw 0x26effe2b9f7f8ae5 0x44ddffc573eff15c 0xfffffe7f9fff9fe7 0xffffffcff3fff3fc

def z6 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x47ffffffe0000007 0xe8fffffffc000000

def z7 : W := mkw 0x108000001a405100 0x0210000003480a20 0x000000000c601980 0x00000000018c0330

def z8 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xf7fffe001fff8003 0xfeffffc003fff000

def z9 : W := mkw 0x0a05c02144180856 0x0140b8042883010a 0x0007c001e01c007a 0x0000f8003c03800f

def z10 : W := mkw 0x1458009402c02500 0x028b0012805804a0 0x1078001e03e00781 0x020f0003c07c00f0

def z11 : W := mkw 0x066f280000000000 0x00cde50000000000 0x47fffe0000000003 0xe8ffffc000000000

def z12 : W := mkw 0x4ffffdfffc185856 0x09ffffbfff830b0a 0xeffffffffc1c787f 0xfdffffffff838f0f

def z13 : W := mkw 0x038541401c185000 0x0070a82803830a00 0xef87c1e01c1c7806 0xfdf0f83c03838f00

def z14 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0x77f8019e13e06781 0x4eff0033c27c0cf0

def z15 : W := mkw 0x15d8d7ff9ef1ffe5 0x42bb1afff3de3ffc 0xfff9ffff9ff3ffe7 0xffff3ffff3fe7ffc

def z16 : W := mkw 0x477fbdffe186a629 0x88eff7bffc30d4c5 0xfffffffff39fe67f 0xfffffffffe73fccf

def z17 : W := mkw 0x0000420004310000 0x0000084000862000 0x9009fe000c738003 0xb2013fc0018e7000

def z18 : W := mkw 0x0000000000000000 0x0000000000000000 0xa8060181f01c607e 0x7500c0303e038c0f

def z19 : W := mkw 0x246a2a0003670000 0x048d4540006ce000 0x10783e0003e38001 0x020f07c0007c7000

def z20 : W := mkw 0x0000100880008221 0x0000020110001044 0xb8063199f01fe67f 0x7700c6333e03fccf

def z21 : W := mkw 0x15c801441a405100 0x02b9002883480a20 0x478800660c601980 0x88f1000cc18c0330

def z22 : W := mkw 0x208042001f7f0000 0x0410084003efe000 0xb00000001fff8000 0x1600000003fff000

def z23 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0xef81c1e01c007804 0xfdf0383c03800f00

def z24 : W := mkw 0x15d801d41bc6f729 0x82bb003a8378dee5 0xfff801fe1ffffffd 0xffff003fc3ffffff

def z25 : W := mkw 0x1000000002c02500 0x02000000005804a0 0x1000000003e00780 0x02000000007c00f0

def z26 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0x1070301803838601 0x020e0603007070c0

def z27 : W := mkw 0x0bb7f1f9fd9efe7f 0x8176fe3f3fb3dfcf 0xfff7f1f9ff9ffe7f 0xfffefe3f3ff3ffcf

def z28 : W := mkw 0x0022200001060000 0x000444000020c000 0x00063000001f8002 0x0000c6000003f000

def z29 : W := mkw 0x067f3898a0000000 0x00cfe71314000000 0x47ffff99e0000007 0xe8fffff33c000000

def z30 : W := mkw 0x119001d41ac07500 0x0232003a83580ea0 0xb80001fe1fe07f84 0x1700003fc3fc0ff0

def z31 : W := mkw 0x0000000001060000 0x000000000020c000 0xb0000000139f8000 0x160000000273f000

def z32 : W := mkw 0x55d895fffac07500 0x0abb12bfff580ea0 0xfff801ffffe07f85 0xffff003ffffc0ff0

def z33 : W := mkw 0x0032b4bba186a629 0x800656977430d4c5 0xb87ffffff39fe67f 0xf70ffffffe73fccf

def z34 : W := mkw 0x118001401ac07500 0x0230002803580ea0 0xff8001e01fe07f84 0xfff0003c03fc0ff0

def z35 : W := mkw 0x22a76a001f7f0000 0x0454ed4003efe000 0xb007fe001fff8002 0x1600ffc003fff000

def z36 : W := mkw 0x0900956bc000daf7 0x412012ad78001b5e 0x080001ffe0007ffc 0x0100003ffc000fff

def z37 : W := mkw 0x0000020000210000 0x0000004000042000 0x10083e0000638001 0x020107c0000c7000

def z38 : W := mkw 0x0000420004318ae5 0x400008400086315c 0x980000000c739fe0 0x13000000018e73fc

def z39 : W := mkw 0x1fdd01d45ac87512 0x03fba03a8b590ea2 0x67f60180738c6018 0x4cfec0300e718c03

def z40 : W := mkw 0x0900816140005856 0x0120102c28000b0a 0x080001e1e000787c 0x0100003c3c000f0f

def z41 : W := mkw 0x0305816140000000 0x0060b02c28000000 0x4787c1e1e0000006 0xe8f0f83c3c000000

def z42 : W := mkw 0x000000000186a629 0x800000000030d4c5 0xb8060181f39fe67e 0x7700c0303e73fccf

def z43 : W := mkw 0x04c842001e710000 0x0099084003ce2000 0xf7f9fe001ff38003 0xfeff3fc003fe7000

def z44 : W := mkw 0x0000802100000844 0x0000100420000108 0x0800006180001864 0x0100000c3000030c

def z45 : W := mkw 0x246a6a0007770000 0x048d4d4000eee000 0x9079fe000ff38003 0xb20f3fc001fe7000

def z46 : W := mkw 0x37ff6bd41fff7500 0x06ffed7a83ffeea0 0xfffffffe1fffff87 0xffffffffc3fffff0

def z47 : W := mkw 0x474d8d6740000000 0x08e9b1ace8000000 0x4789ce6600000000 0x88f139ccc0000000

def z48 : W := mkw 0x028540001c180000 0x0050a80003830000 0xe787c0001c1c0002 0xfcf0f80003838000

def z49 : W := mkw 0x477fbdffe1862408 0x88eff7bffc30c481 0x67fffffff38c601f 0xecfffffffe718c03

def z50 : W := mkw 0x0032369aa1a7a6a9 0xc00646d35434f4d5 0xb87e3f9ff3ffe7ff 0x770fc7f3fe7ffcff

def z51 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0x6787c181f01c607a 0x4cf0f8303e038c0f

def z52 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0x67f7fe00139f8002 0x4cfeffc00273f000

def z53 : W := mkw 0x0b85d56bdc185856 0x0170baad7b830b0a 0xef8ffffffc1c787f 0xfdf1ffffff838f0f

def z54 : W := mkw 0x15c801441ac07500 0x02b9002883580ea0 0xff8800661fe07f80 0x9ff1000cc3fc0ff0

def z55 : W := mkw 0x088040001c185856 0x0110080003830b0a 0xa80000001c1c7878 0x1500000003838f0f

def z56 : W := mkw 0x1dd881f55ac07d56 0x03bb103eab580faa 0xfff801ffffe07ffd 0xffff003ffffc0fff

def z57 : W := mkw 0x57ff29d47ac07500 0x0affe53a8f580ea0 0x67f6018073806000 0x4cfec0300e700c00

def z58 : W := mkw 0x0305956bc0000000 0x0060b2ad78000000 0x478fffffe0000007 0xe8f1fffffc000000

def z59 : W := mkw 0x0010009000802400 0x0002001200100480 0xb870019813806605 0x770e003302700cc0

def z60 : W := mkw 0x26ff7a98bfffa629 0x84dfef5317fff4c5 0xffffff99ffffe67f 0xfffffff33ffffccf

def z61 : W := mkw 0x0180014018005000 0x0030002803000a00 0xef8001e01c007804 0xfdf0003c03800f00

def z62 : W := mkw 0x191081f540807d56 0x0322103ea8100faa 0x080001ffe0007ffc 0x0100003ffc000fff

def z63 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0x67f0018013806000 0x4cfe003002700c00

def z64 : W := mkw 0x26ef28001b4e0000 0x04dde5000369c000 0x67f60000138c0000 0x4cfec00002718000

def z65 : W := mkw 0x4337bdffe0000000 0x0866f7bffc000000 0x0007ffffe0000006 0x0000fffffc000000

def z66 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0x6ff001fe13807f84 0x4dfe003fc2700ff0

def z67 : W := mkw 0x00223008a0000000 0x0004460114000000 0x00063001e0000002 0x0000c6003c000000

def z68 : W := mkw 0x26cdde2b9e798ae5 0x44d9bbc573cf315c 0xdf89fe7f8c739fe7 0xbbf13fcff18e73fc

def z69 : W := mkw 0x6fffffffff7f5856 0x0dffffffffefeb0a 0xfffffffffffff87f 0xffffffffffffff0f

def z70 : W := mkw 0x447a3c9ea0000000 0x088f4793d4000000 0x00783e1e00000001 0x000f07c3c0000000

def z71 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z72 : W := mkw 0x677fbfffe3670000 0x0ceff7fffc6ce000 0x57ffffffe3e38007 0xeafffffffc7c7000

def z73 : W := mkw 0x00101098a080a629 0x80020213141014c5 0xb8700199f380667d 0x770e00333e700ccf

def z74 : W := mkw 0x0000942b80000000 0x0000128570000000 0x0009fe7f80000007 0xa0013fcff0000000

def z75 : W := mkw 0x477f29d460000000 0x08efe53a8c000000 0x47f6018060000000 0x48fec0300c000000

def z76 : W := mkw 0x477fbdffe0802400 0x08eff7bffc100480 0xfffffffff3806607 0xfffffffffe700cc0

def z77 : W := mkw 0x15fa21d41bc67500 0x02bf443a8378cea0 0xfffe31fe1fffff87 0xffffc63fc3fffff0

def z78 : W := mkw 0x0000000000000000 0x0000000000000000 0x9808007e0c601f85 0xb301000fc18c03f0

def z79 : W := mkw 0x108000001ac07500 0x0210000003580ea0 0xb80000001fe07f80 0x1700000003fc0ff0

def z80 : W := mkw 0x0305816140000000 0x0060b02c28000000 0x4781c06000000000 0x88f0380c00000000

def z81 : W := mkw 0x22276a00053f0000 0x0444ed4000a7e000 0x0007fe00001f8002 0x0000ffc00003f000

def z82 : W := mkw 0x0337b1f9e186a629 0x8066f63f3c30d4c5 0xfff7f1f9f39fe67f 0xfffefe3f3e73fccf

def z83 : W := mkw 0x0032f6bba5b7aeed 0xc0065ed774b6f5dd 0xb87fffffffffffff 0xf70fffffffffffff

def z84 : W := mkw 0x0000c623043108c4 0x400018c460862118 0x0009ce660c601980 0x800139ccc18c0330

def z85 : W := mkw 0x0b85014058085012 0x0170a0280b010a02 0x67860180700c6018 0x4cf0c0300e018c03

def z86 : W := mkw 0x108042001ef1ffe5 0x4210084003de3ffc 0xb80000001ff3ffe0 0x1700000003fe7ffc

def z87 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0x4781c0600c001800 0x88f0380c01800300

def z88 : W := mkw 0x055801d400000000 0x00ab003a80000000 0x47f801fe00000005 0xe8ff003fc0000000

def z89 : W := mkw 0x147a309ca3c6a729 0x828f46139478d4e5 0xb87e319ff3ffe7ff 0x770fc633fe7ffcff

def z90 : W := mkw 0x0000000000802400 0x0000000000100480 0xb800000013806600 0x1700000002700cc0

def z91 : W := mkw 0x411095ffe0000000 0x082212bffc000000 0x000001ffe0000004 0x0000003ffc000000

def z92 : W := mkw 0x266f2a0003670000 0x04cde540006ce000 0x57fffe0003e38003 0xeaffffc0007c7000

def z93 : W := mkw 0x57ffbdfffac07500 0x0afff7bfff580ea0 0xffffffffffe07f87 0xfffffffffffc0ff0

def z94 : W := mkw 0x20b27298bfffa629 0x84164e5317fff4c5 0xb8763199ffffe67f 0x770ec6333ffffccf

def z95 : W := mkw 0x008040001c180000 0x0010080003830000 0xa00000001c1c0000 0x1400000003838000

def z96 : W := mkw 0x0000000000000000 0x0000000000000000 0x980000000c601f80 0x13000000018c03f0

def z97 : W := mkw 0x111095ff8080ffe5 0x422212bff0101ffc 0x080001ff80007fe4 0x0100003ff0000ffc

def z98 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x9800007f8c739fe4 0x1300000ff18e73fc

def z99 : W := mkw 0x1fddc1f55ed87d56 0x03fbb83eabdb0faa 0xffffc1fffffc7fff 0xfffff83fffff8fff

def z100 : W := mkw 0x0000420004318ae5 0x400008400086315c 0x9809fe000c739fe3 0xb3013fc0018e73fc

def z101 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0x9870301983938667 0x330e0603307270cc

def z102 : W := mkw 0x0bb721d0798e741a 0x8176e43a0f31ce83 0x67f60180738c6018 0x4cfec0300e718c03

def z103 : W := mkw 0x308042001fff7500 0x0610084003ffeea0 0xb80000001fffff80 0x1700000003fffff0

def z104 : W := mkw 0x0010009000802400 0x0002001200100480 0x0800019800006604 0x0100003300000cc0

def z105 : W := mkw 0x477f29d461862408 0x88efe53a8c30c481 0x67f60180738c6018 0x4cfec0300e718c03

def z106 : W := mkw 0x0305816140000000 0x0060b02c28000000 0xef87c1e1f01c607e 0xfdf0f83c3e038c0f

def z107 : W := mkw 0x577fbdffe2c02500 0x0aeff7bffc5804a0 0x57ffffffe3e00787 0xeafffffffc7c00f0

def z108 : W := mkw 0x2fefeb615f7f5856 0x05fdfd6c2befeb0a 0xffffffe1fffff87f 0xfffffffc3fffff0f

def z109 : W := mkw 0x57ffbdfffac07500 0x0afff7bfff580ea0 0x67fffffff3806007 0xecfffffffe700c00

def z110 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0xfffe01fffffc7fff 0xffffc03fffff8fff

def z111 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xffffff81ffffe07f 0xfffffff03ffffc0f

def z112 : W := mkw 0x26cd4a001e790000 0x04d9a94003cf2000 0xf7f9ce001fe00001 0xfeff39c003fc0000

def z113 : W := mkw 0x0bb7f1f9fc185856 0x0176fe3f3f830b0a 0xeff7f1f9fc1c787f 0xfdfefe3f3f838f0f

def z114 : W := mkw 0x01b231d8b986f629 0x8036463b1730dec5 0xfff631f9ff9ffe7f 0xfffec63f3ff3ffcf

def z115 : W := mkw 0x647a3e9ea3670000 0x0c8f47d3d46ce000 0x10783e1e03e38001 0x020f07c3c07c7000

def z116 : W := mkw 0x04c800001a400000 0x0099000003480000 0xfff8007e1fe01f85 0xffff000fc3fc03f0

def z117 : W := mkw 0x22054a0004390000 0x0440a94000872000 0x0001ce0000000000 0x000039c000000000

def z118 : W := mkw 0x00101098a080a629 0x80020213141014c5 0x08000199e000667c 0x010000333c000ccf

def z119 : W := mkw 0x111001d400807500 0x0222003a80100ea0 0x080001fe00007f84 0x0100003fc0000ff0

def z120 : W := mkw 0x1b95c1f55c987d56 0x0372b83eab930faa 0xef87c1fffc1c7ffe 0xfdf0f83fff838fff

def z121 : W := mkw 0x577fbdffe0807500 0x0aeff7bffc100ea0 0x4fffffffe0007f87 0xe9fffffffc000ff0

def z122 : W := mkw 0x26ff6a901fff2400 0x04dfed5203ffe480 0xffffff981fffe607 0xfffffff303fffcc0

def z123 : W := mkw 0x04c800001a400000 0x0099000003480000 0x478800000c600000 0x88f10000018c0000

def z124 : W := mkw 0x67ffffffffffa629 0x8cfffffffffff4c5 0xffffffffffffe67f 0xfffffffffffffccf

def z125 : W := mkw 0x1010009400802500 0x02020012801004a0 0x0000001e00000780 0x00000003c00000f0

def z126 : W := mkw 0x0100816140000000 0x0020102c28000000 0x000001e1e0000004 0x0000003c3c000000

def z127 : W := mkw 0x0032209021862408 0x800644120430c481 0x20760180738c6018 0x440ec0300e718c03

def z128 : W := mkw 0x477fffffe4318ae5 0x48effffffc86315c 0xdfffffffec739fe7 0xfbfffffffd8e73fc

def z129 : W := mkw 0x474ddf6fc4318ae5 0x48e9bbedf886315c 0xdf89fe7f8c739fe7 0xbbf13fcff18e73fc

def z130 : W := mkw 0x0000100880008221 0x0000020110001044 0x9800301980138667 0x33000603300270cc

def z131 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0060000101c0002 0x7400c00002038000

def z132 : W := mkw 0x22277a08a53f8229 0x8444ef4114a7f045 0x0007fe01e01f807a 0x0000ffc03c03f00f

def z133 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0xe787c0601c1c1802 0xfcf0f80c03838300

def z134 : W := mkw 0x109000901ac07500 0x0212001203580ea0 0xb87001981fe07f85 0x770e003303fc0ff0

def z135 : W := mkw 0x0458009400000000 0x008b001280000000 0x0078001e00000001 0x000f0003c0000000

def z136 : W := mkw 0x0032f6bba5b7aeed 0xc0065ed774b6f5dd 0xb877ff99f39fe67f 0x770efff33e73fccf

def z137 : W := mkw 0x0000420004310000 0x0000084000862000 0x0001fe0000138002 0x00003fc000027000

def z138 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x0001fe0180138062 0x00003fc03002700c

def z139 : W := mkw 0x411095ffe0008ae5 0x482212bffc00115c 0x080001ffe0001fe4 0x0100003ffc0003fc

def z140 : W := mkw 0x0000d02984108a65 0x00001a053082114c 0x9801f0798c139e67 0xb3003e0f318273cc

def z141 : W := mkw 0x42058c2340000000 0x0840b18468000000 0x0001ce0000000000 0x000039c000000000

def z142 : W := mkw 0x447a3c9ea186a629 0x888f4793d430d4c5 0xb87e3f9ff39fe67f 0x770fc7f3fe73fccf

def z143 : W := mkw 0x0000420004310000 0x0000084000862000 0x0009ce000c600000 0x800139c0018c0000

def z144 : W := mkw 0x00223008a1068229 0x800446011420d045 0x00063001e01f807a 0x0000c6003c03f00f

def z145 : W := mkw 0x477fbdffe080a629 0x88eff7bffc1014c5 0x4fffffffe000667f 0xe9fffffffc000ccf

def z146 : W := mkw 0x0000942b80008221 0x0000128570001044 0x9809fe7f80138667 0xb3013fcff00270cc

def z147 : W := mkw 0x0b85d76bdc39daf7 0x4170baed7b873b5e 0xff8ffffffc7fffff 0xfff1ffffff8fffff

def z148 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0x20763181f39fe07a 0x440ec6303e73fc0f

def z149 : W := mkw 0x0022200001060000 0x000444000020c000 0xb0763000139f8003 0x760ec6000273f000

def z150 : W := mkw 0x0180014018005000 0x0030002803000a00 0xef8601e1fc1c787e 0xfdf0c03c3f838f0f

def z151 : W := mkw 0x477fbdffe0008ae5 0x48eff7bffc00115c 0x4fffffffe0001fe7 0xe9fffffffc0003fc

def z152 : W := mkw 0x0000160a802182a1 0x400002c150043054 0x98083e7e0c639f85 0xb30107cfc18c73f0

def z153 : W := mkw 0x288042001f7f5856 0x0510084003efeb0a 0xb80000001ffff878 0x1700000003ffff0f

def z154 : W := mkw 0x467f3c9ea0000000 0x08cfe793d4000000 0x47fffe1e00000003 0xe8ffffc3c0000000

def z155 : W := mkw 0x15d811dc9ac0f721 0x02bb023b93581ee4 0xfff831ff9ff3ffe7 0xffff063ff3fe7ffc

def z156 : W := mkw 0x0b85014058085012 0x0170a0280b010a02 0xef860181f01c607e 0x7df0c0303e038c0f

def z157 : W := mkw 0x0a05c02144180856 0x0140b8042883010a 0x8807c061ec1c187e 0xb100f80c3d83830f

def z158 : W := mkw 0x0010d6bba4b1aeed 0xc0021ad7749635dd 0x9809ffffec73ffff 0xb3013ffffd8e7fff

def z159 : W := mkw 0x00323098a0000000 0x0006461314000000 0x00763199e0000007 0x600ec6333c000000

def z160 : W := mkw 0x0285000018080000 0x0050a00003010000 0x67860000100c0000 0x4cf0c00002018000

def z161 : W := mkw 0x477fbdffe186a629 0x88eff7bffc30d4c5 0x57ffffffe3838607 0xeafffffffc7070c0

def z162 : W := mkw 0x0980816158005856 0x0130102c2b000b0a 0xef8001e1fc00787c 0xfdf0003c3f800f0f

def z163 : W := mkw 0x547a3c9ea2c02500 0x0a8f4793d45804a0 0x10783e1e03e00781 0x020f07c3c07c00f0

def z164 : W := mkw 0x35d843d41fff7500 0x06bb087a83ffeea0 0xfff801fe1fffff85 0xffff003fc3fffff0

def z165 : W := mkw 0x0032209020000000 0x0006441204000000 0x0076018060000000 0x400ec0300c000000

def z166 : W := mkw 0x1dd841d41ed87d56 0x03bb083a83db0faa 0xfff801fe1ffc7ffd 0xffff003fc3ff8fff

def z167 : W := mkw 0x47ffbdfffa400000 0x08fff7bfff480000 0xf7ffffffffe00007 0xfefffffffffc0000

def z168 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x9009fe018c738063 0xb2013fc0318e700c

def z169 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0xdfffffffec601f87 0xfbfffffffd8c03f0

def z170 : W := mkw 0x055801d400000000 0x00ab003a80000000 0xdff801fe0c601f85 0xfbff003fc18c03f0

def z171 : W := mkw 0x4fcdcd675c185856 0x09f9b9aceb830b0a 0xef8fcfe7fc1c787e 0xfdf1f9fcff838f0f

def z172 : W := mkw 0x4227bc2be0000000 0x0844f7857c000000 0x0007fe01e0000002 0x0000ffc03c000000

def z173 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0xef81c0601c1c7878 0x9df0380c03838f0f

def z174 : W := mkw 0x0227280000000000 0x0044e50000000000 0x0007fe0000000002 0x0000ffc000000000

def z175 : W := mkw 0x477f29d460000000 0x08efe53a8c000000 0x47ffff8060000003 0xe8fffff00c000000

def z176 : W := mkw 0x15d895ff9ac07500 0x02bb12bff3580ea0 0xfff9ffff9fe07f87 0xffff3ffff3fc0ff0

def z177 : W := mkw 0x477fbdffe1060000 0x08eff7bffc20c000 0xf7fffffff39f8007 0xfefffffffe73f000

def z178 : W := mkw 0x0880d62b9c39daf7 0x41101ac573873b5e 0xb809fe7f9c7fffff 0xb7013fcff38fffff

def z179 : W := mkw 0x447abcbfa0000000 0x088f5797f4000000 0x0079fe7f80000007 0xa00f3fcff0000000

def z180 : W := mkw 0x26cd4a001e790000 0x04d9a94003cf2000 0x4789ce000c600000 0x88f139c0018c0000

def z181 : W := mkw 0x0022f62ba5378aed 0xc0045ec574a6f15d 0x980ffe7fec7f9fff 0xb301ffcffd8ff3ff

def z182 : W := mkw 0x0000000000008221 0x0000000000001044 0x9800000000138660 0x13000000000270cc

def z183 : W := mkw 0x26cd4a001e790000 0x04d9a94003cf2000 0xd789fe000c738003 0xbaf13fc0018e7000

def z184 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0xff8fc1fffc7c7fff 0xfff1f83fff8f8fff

def z185 : W := mkw 0x26ef28001b4e0000 0x04dde5000369c000 0xf7fe00001fec0001 0xfeffc00003fd8000

def z186 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0x57f8007e0fe01f81 0x8aff000fc1fc03f0

def z187 : W := mkw 0x0000000001068229 0x800000000020d045 0x00000000001f8078 0x000000000003f00f

def z188 : W := mkw 0x476fad6740000000 0x08edf5ace8000000 0x47fffe6600000003 0xe8ffffccc0000000

def z189 : W := mkw 0x22272800010e0000 0x0444e5000021c000 0x00060000000c0000 0x0000c00000018000

def z190 : W := mkw 0x0022200021060008 0x800444000420c001 0x00060000600c0018 0x0000c0000c018003

def z191 : W := mkw 0x0000000000000000 0x0000000000000000 0x0800007e00001f84 0x0100000fc00003f0

def z192 : W := mkw 0x474d8d6740000000 0x08e9b1ace8000000 0x478fcfe7e0000006 0xe8f1f9fcfc000000

def z193 : W := mkw 0x2fcdcb615e795856 0x05f9b96c2bcf2b0a 0x4789ce600c601800 0x88f139cc018c0300

def z194 : W := mkw 0x0000c623043108c4 0x400018c460862118 0x0001ce0000000000 0x000039c000000000

def z195 : W := mkw 0x20a262001f7f0000 0x04144c4003efe000 0xb07630001fff8003 0x760ec60003fff000

def z196 : W := mkw 0x06ef68001c180000 0x00dded0003830000 0xe7fffe001c1c0003 0xfcffffc003838000

def z197 : W := mkw 0x17ff29d41ac07500 0x02ffe53a83580ea0 0xfffffffe1fe07f87 0xffffffffc3fc0ff0

def z198 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0x67f801fe13806005 0xecff003fc2700c00

def z199 : W := mkw 0x000000000186a629 0x800000000030d4c5 0xb8000000139fe678 0x170000000273fccf

def z200 : W := mkw 0x474d094440000000 0x08e9a12888000000 0x4780000000000000 0x08f0000000000000

def z201 : W := mkw 0x208042001e790000 0x0410084003cf2000 0x000000000c600000 0x00000000018c0000

def z202 : W := mkw 0x0000c02104100844 0x0000180420820108 0x0001c00180100062 0x000038003002000c

def z203 : W := mkw 0x411095ffe080a629 0x882212bffc1014c5 0x080001ffe000667c 0x0100003ffc000ccf

def z204 : W := mkw 0x05d801d418005000 0x00bb003a83000a00 0xeff801fe1c007805 0xfdff003fc3800f00

def z205 : W := mkw 0x15d8c1f51ed07d44 0x02bb183ea3da0fa8 0xfff9c1ff9ff07fe7 0xffff383ff3fe0ffc

def z206 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x47f7ff81e0000002 0x48fefff03c000000

def z207 : W := mkw 0x2227fe2b853f8ae5 0x4444ffc570a7f15c 0x0007fe01801f8062 0x0000ffc03003f00c

def z208 : W := mkw 0x0900c16144105856 0x0120182c28820b0a 0x8801c1e1ec10787e 0xb100383c3d820f0f

def z209 : W := mkw 0x0080000018005000 0x0010000003000a00 0xa80000001c007800 0x1500000003800f00

def z210 : W := mkw 0x0205400004180000 0x0040a80000830000 0x0007c000001c0002 0x0000f80000038000

def z211 : W := mkw 0x37ff29d41bce7500 0x06ffe53a8379cea0 0x67f60180138c6000 0x4cfec03002718c00

def z212 : W := mkw 0x0fefe9615c185856 0x01fdfd2c2b830b0a 0xefffffe1fc1c787f 0xfdfffffc3f838f0f

def z213 : W := mkw 0x0180014018005000 0x0030002803000a00 0x6780018010006000 0x4cf0003002000c00

def z214 : W := mkw 0x0b85d76bdc39daf7 0x4170baed7b873b5e 0xdf89fe7f8c739fe7 0xbbf13fcff18e73fc

def z215 : W := mkw 0x0000942b80008ae5 0x400012857000115c 0x9800307f80139fe7 0x3300060ff00273fc

def z216 : W := mkw 0x67ffffffff7f0000 0x0cffffffffefe000 0xf7ffffffffff8007 0xfefffffffffff000

def z217 : W := mkw 0x0000160a802182a1 0x400002c150043054 0x10083e1e00638781 0x020107c3c00c70f0

def z218 : W := mkw 0x066fbc2b80000000 0x00cdf78570000000 0x47fffe7f80000007 0xe8ffffcff0000000

def z219 : W := mkw 0x0022200001060000 0x000444000020c000 0xb8763181f39fe07f 0x770ec6303e73fc0f

def z220 : W := mkw 0x0000942b80008ae5 0x400012857000115c 0x9808007f8c601fe5 0xb301000ff18c03fc

def z221 : W := mkw 0x37ffffff9fffffe5 0x46fffffff3fffffc 0xffffffff9fffffe7 0xfffffffff3fffffc

def z222 : W := mkw 0x04c800001a400000 0x0099000003480000 0x67f0000013800000 0x4cfe000002700000

def z223 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x1009fe7e0c639f81 0x82013fcfc18c73f0

def z224 : W := mkw 0x0a05c02144180856 0x0140b8042883010a 0x0001c00000000000 0x0000380000000000

def z225 : W := mkw 0x477fffffe43108c4 0x48effffffc862118 0x47ffffffec601987 0xe8fffffffd8c0330

def z226 : W := mkw 0x474d9d6fc0000000 0x08e9b3adf8000000 0x4789fe7f80000007 0xa8f13fcff0000000

def z227 : W := mkw 0x1ffff1fdffdeff7f 0x83fffe3fbffbdfef 0xfffff1ffffffffff 0xfffffe3fffffffff

def z228 : W := mkw 0x27efeb615f7f0000 0x04fdfd6c2befe000 0xf7ffffe1ffff8007 0xfefffffc3ffff000

def z229 : W := mkw 0x0000802100000000 0x0000100420000000 0x0001c06180000006 0xa000380c30000000

def z230 : W := mkw 0x00323098a1068229 0x800646131420d045 0x00763199e01f807f 0x600ec6333c03f00f

def z231 : W := mkw 0x0ba7f169fd1eda7f 0x8174fe2d3fa3db4f 0xef87f1e1fc1ff87e 0xfdf0fe3c3f83ff0f

def z232 : W := mkw 0x05c801401a405000 0x00b9002803480a00 0xfff801e01fe07805 0xffff003c03fc0f00

def z233 : W := mkw 0x26ff6a903fff2408 0x84dfed5207ffe481 0xf7ffff807fffe01b 0xfefffff00ffffc03

def z234 : W := mkw 0x57ffbdfffbc6f729 0x8afff7bfff78dee5 0xffffffffffffffff 0xffffffffffffffff

def z235 : W := mkw 0x0000942b80008ae5 0x400012857000115c 0x0809fe7f80001fe7 0xa1013fcff00003fc

def z236 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0x6787c1e07c0c7818 0xccf0f83c0f818f03

def z237 : W := mkw 0x0000000000000000 0x0000000000000000 0xa800018010006004 0x7500003002000c00

def z238 : W := mkw 0x075d81f540000000 0x00ebb03ea8000000 0x47ffc1ffe0000007 0xe8fff83ffc000000

def z239 : W := mkw 0x077f29d400000000 0x00efe53a80000000 0x47fffffe00000007 0xe8ffffffc0000000

def z240 : W := mkw 0x0a8540001c185856 0x0150a80003830b0a 0xef87c0001c1c787a 0xfdf0f80003838f0f

def z241 : W := mkw 0x0000100880008221 0x0000020110001044 0x0800001980000664 0x01000003300000cc

def z242 : W := mkw 0x0880c0211c185856 0x0110180423830b0a 0xa801c0619c1c787e 0xb500380c33838f0f

def z243 : W := mkw 0x15d801d41a405100 0x02bb003a83480a20 0x47f801fe0c601985 0xe8ff003fc18c0330

def z244 : W := mkw 0x26effe2b9f7f8ae5 0x44ddffc573eff15c 0xf7fffe019fff8063 0xfeffffc033fff00c

def z245 : W := mkw 0x0000942b80000000 0x0000128570000000 0x0000007f80000004 0x0000000ff0000000

def z246 : W := mkw 0x2fef29405b4e5012 0x05fde5280b69ca02 0x67f60180738c6018 0x4cfec0300e718c03

def z247 : W := mkw 0x0b85c3615c395856 0x0170b86c2b872b0a 0xff8fffe1fc7ff87f 0xfff1fffc3f8fff0f

def z248 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0x57f9fe000fe38001 0x8aff3fc001fc7000

def z249 : W := mkw 0x088040001c185856 0x0110080003830b0a 0x000000000c001800 0x0000000001800300

def z250 : W := mkw 0x36ff6a941fff2500 0x06dfed5283ffe4a0 0xf7fffe1e1fff8783 0xfeffffc3c3fff0f0

def z251 : W := mkw 0x0000c02104100844 0x0000180420820108 0x8801c0618c101866 0xb100380c3182030c

def z252 : W := mkw 0x155801d402c02500 0x02ab003a805804a0 0x57f801fe03e00785 0xeaff003fc07c00f0

def z253 : W := mkw 0x0000420004310000 0x0000084000862000 0x900000000c738000 0x12000000018e7000

def z254 : W := mkw 0x26ef7a089f7f8221 0x04ddef4113eff044 0xfffffe199fff8667 0xffffffc333fff0cc

def z255 : W := mkw 0x447a3c9ea186a629 0x888f4793d430d4c5 0x10783e1e03838601 0x020f07c3c07070c0

def z256 : W := mkw 0x0032209001862400 0x000644120030c480 0xb8763198139fe607 0x770ec6330273fcc0

def z257 : W := mkw 0x477fbdffe0008221 0x08eff7bffc001044 0xdfffffffe0138667 0xfbfffffffc0270cc

def z258 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0x10763019e39f867b 0x020ec6033c73f0cf

def z259 : W := mkw 0x4000942be0000000 0x080012857c000000 0x00000001e0000000 0x000000003c000000

def z260 : W := mkw 0x00223008a1068229 0x800446011420d045 0xb0763001f39f807b 0x760ec6003e73f00f

def z261 : W := mkw 0x4237bcbbe0000000 0x0846f7977c000000 0x0077ff99e0000007 0x600efff33c000000

def z262 : W := mkw 0x066f280000000000 0x00cde50000000000 0x47f6000000000000 0x48fec00000000000

def z263 : W := mkw 0x4b95d5fffc185856 0x0972babfff830b0a 0xef87c1fffc1c787e 0xfdf0f83fff838f0f

def z264 : W := mkw 0x00223008a1068229 0x800446011420d045 0x0000300000038000 0x0000060000007000

def z265 : W := mkw 0x0305d76bc4318ae5 0x4060baed7886315c 0xdf8fffffec739fe7 0xfbf1fffffd8e73fc

def z266 : W := mkw 0x476fbd6fe0000000 0x08edf7adfc000000 0x478ffe67e0000002 0x88f1ffccfc000000

def z267 : W := mkw 0x26ef28001b4e0000 0x04dde5000369c000 0xf7f63000139f8003 0x7efec6000273f000

def z268 : W := mkw 0x15fa21d43bc67508 0x82bf443a8778cea1 0xfffe01fe7fec7f9d 0xffffc03fcffd8ff3

def z269 : W := mkw 0x4010149ea0000000 0x08020293d4000000 0x0000001e00000000 0x00000003c0000000

def z270 : W := mkw 0x4fcdcd675c185856 0x09f9b9aceb830b0a 0x4789ce660c001800 0x88f139ccc1800300

def z271 : W := mkw 0x2eef6a001f7f5856 0x05dded4003efeb0a 0xfffffe001ffff87b 0xffffffc003ffff0f

def z272 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0xcf81c0618c101866 0xb9f0380c3182030c

def z273 : W := mkw 0x247a3a98a3e7a629 0x848f4753147cf4c5 0xb87e3f99f3ffe67f 0x770fc7f33e7ffccf

def z274 : W := mkw 0x477f3ddee0000000 0x08efe7bbdc000000 0x47fe3f9e60000001 0x48ffc7f3cc000000

def z275 : W := mkw 0x15fa31dcbbc6f729 0x82bf463b9778dee5 0xfffe31ffffffffff 0xffffc63fffffffff

def z276 : W := mkw 0x00323098a0802400 0x0006461314100480 0xb8763199f3806607 0x770ec6333e700cc0

def z277 : W := mkw 0x066ffe2b84318ae5 0x40cdffc57086315c 0xdffffe7f8c739fe7 0xfbffffcff18e73fc

def z278 : W := mkw 0x4132b5ffe186a629 0x882656bffc30d4c5 0xb87631fff39fe67f 0x770ec63ffe73fccf

def z279 : W := mkw 0x00327298a5b7aeed 0xc0064e5314b6f5dd 0xb8763199ffffffff 0x770ec6333fffffff

def z280 : W := mkw 0x4ffffdfffc185856 0x09ffffbfff830b0a 0x47ffffffec001807 0xe8fffffffd800300

def z281 : W := mkw 0x26ef6a001e790000 0x04dded4003cf2000 0x47fffe000c600003 0xe8ffffc0018c0000

def z282 : W := mkw 0x0000560a843182a1 0x40000ac150863054 0x9009fe1e0c738783 0xb2013fc3c18e70f0

def z283 : W := mkw 0x0032369aa1a7a6a9 0xc00646d35434f4d5 0x10783e1e03e38781 0x020f07c3c07c70f0

def z284 : W := mkw 0x477fbdffe1068229 0x88eff7bffc20d045 0x47ffffffe01f807f 0xe8fffffffc03f00f

def z285 : W := mkw 0x076fa96140000000 0x00edf52c28000000 0x47ffffe1e0000007 0xe8fffffc3c000000

def z286 : W := mkw 0x26efea211f7f0844 0x04ddfd4423efe108 0xfffffe619fff9867 0xffffffcc33fff30c

def z287 : W := mkw 0x066f280001060000 0x00cde5000020c000 0xf7fffe00139f8003 0xfeffffc00273f000

def z288 : W := mkw 0x0000420004310000 0x0000084000862000 0x9809fe7e0c739f87 0xb3013fcfc18e73f0

def z289 : W := mkw 0x001000900186a629 0x800200120030d4c5 0xb8700198139fe67d 0x770e00330273fccf

def z290 : W := mkw 0x0000000000000000 0x0000000000000000 0x00060001e01c007a 0x0000c0003c03800f

def z291 : W := mkw 0x0285d62b9c398ae5 0x4050bac57387315c 0xff8ffe7f9c7f9fe7 0xfff1ffcff38ff3fc

def z292 : W := mkw 0x4a27fc2be4180856 0x0944ff857c83010a 0x0007fe01e01c007a 0x0000ffc03c03800f

def z293 : W := mkw 0x00323098a080a629 0x80064613141014c5 0x08763199e000667f 0x610ec6333c000ccf

def z294 : W := mkw 0x0a85c0215c185856 0x0150b8042b830b0a 0xa807c001fc1c787a 0x1500f8003f838f0f

def z295 : W := mkw 0x2080d62b9f7f8ae5 0x44101ac573eff15c 0xb809fe7f9fff9fe7 0xb7013fcff3fff3fc

def z296 : W := mkw 0x246a280003460000 0x048d45000068c000 0x0070000003800000 0x000e000000700000

def z297 : W := mkw 0x15fa31dcbbc6f729 0x82bf463b9778dee5 0xfff831fe1fe3ff85 0xffff063fc3fc7ff0

def z298 : W := mkw 0x0385816158005000 0x0070b02c2b000a00 0xef87c1e1fc007806 0xfdf0f83c3f800f00

def z299 : W := mkw 0x67ff29d47b4e0000 0x0cffe53a8f69c000 0x67f60180738c0000 0x4cfec0300e718000

def z300 : W := mkw 0x4327bd6be0000000 0x0864f7ad7c000000 0x4787ffe1e0000006 0xe8f0fffc3c000000

def z301 : W := mkw 0x064d080000000000 0x00c9a10000000000 0x4789ce0000000000 0x88f139c000000000

def z302 : W := mkw 0x2000020003670000 0x04000040006ce000 0x1000000003e38000 0x02000000007c7000

def z303 : W := mkw 0x4fff29d478085012 0x09ffe53a8f010a02 0x67f60180700c6018 0x4cfec0300e018c03

def z304 : W := mkw 0x008000001a400000 0x0010000003480000 0xb00000001fe00000 0x1600000003fc0000

def z305 : W := mkw 0x0800802140000856 0x010010042800010a 0x00000001e0000078 0x000000003c00000f

def z306 : W := mkw 0x37ff7bdcbffff729 0x86ffef7b97fffee5 0xffffffffffffffff 0xffffffffffffffff

def z307 : W := mkw 0x0305c16144100844 0x0060b82c28820108 0xcf87c1e1ec101866 0xf9f0f83c3d82030c

def z308 : W := mkw 0x15d811dcbac0f729 0x82bb023b97581ee5 0xfff801ffffe07ffd 0xffff003ffffc0fff

def z309 : W := mkw 0x055801d400802400 0x00ab003a80100480 0xfff801fe13806605 0xffff003fc2700cc0

def z310 : W := mkw 0x0000000001862408 0x800000000030c481 0x20000000138c6018 0x0400000002718c03

def z311 : W := mkw 0x447a289420000000 0x088f451284000000 0x0070000000000000 0x000e000000000000

def z312 : W := mkw 0x0b95d1f9fc98fe7f 0x8172ba3f3f931fcf 0xef87c1f9fc1c7e7e 0xfdf0f83f3f838fcf

def z313 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x8801fe618c139866 0xb1003fcc3182730c

def z314 : W := mkw 0x0000100880008221 0x0000020110001044 0x1000301800038601 0x02000603000070c0

def z315 : W := mkw 0x04c800001a400000 0x0099000003480000 0xf7f800001fe00001 0xfeff000003fc0000

def z316 : W := mkw 0x247a3a98a3e7a629 0x848f4753147cf4c5 0x10783e1803e38601 0x020f07c3007c70c0

def z317 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0x4787c1e1ec001806 0xe8f0f83c3d800300

def z318 : W := mkw 0x0000842300000000 0x0000108460000000 0x0009ce6600000000 0x800139ccc0000000

def z319 : W := mkw 0x477fadf760000000 0x08eff5beec000000 0x47ffcfe660000000 0xc8fff9fccc000000

def z320 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0xeffffffff01c607f 0xfdfffffffe038c0f

def z321 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x47f9fe7e00000001 0x88ff3fcfc0000000

def z322 : W := mkw 0x0022200000000000 0x0004440000000000 0x0076300000000003 0x600ec60000000000

def z323 : W := mkw 0x00004200043108c4 0x4000084000862118 0x000000000c601980 0x00000000018c0330

def z324 : W := mkw 0x02a760001d1e0000 0x0054ec0003a3c000 0xf7f7f0001f9f8003 0xfefefe0003f3f000

def z325 : W := mkw 0x0000c623043108c4 0x400018c460862118 0x9009fe660c739983 0xb2013fccc18e7330

def z326 : W := mkw 0x15c801441a405100 0x02b9002883480a20 0xf7f800661fe01981 0xfeff000cc3fc0330

def z327 : W := mkw 0x0180d76b9c31dae5 0x40301aed73863b5c 0xff89ffff9c73ffe7 0xfff13ffff38e7ffc

def z328 : W := mkw 0x5ffffdfffed87d56 0x0bffffbfffdb0faa 0xfffffffffffc7fff 0xffffffffffff8fff

def z329 : W := mkw 0x0000c22104318ae5 0x400018442086315c 0x9801c0618c739fe6 0xb300380c318e73fc

def z330 : W := mkw 0x26ff3898bbcea629 0x84dfe7131779d4c5 0xfff63199f39fe67f 0x7ffec6333e73fccf

def z331 : W := mkw 0x57ff29d47ac07500 0x0affe53a8f580ea0 0xfffe01fe7fe07f85 0xffffc03fcffc0ff0

def z332 : W := mkw 0x26ef7a08bf7f8229 0x84ddef4117eff045 0xf7fffe01ffff807b 0xfeffffc03ffff00f

def z333 : W := mkw 0x0900816140005856 0x0120102c28000b0a 0xa80601e1f01c787e 0x7500c03c3e038f0f

def z334 : W := mkw 0x67cdcf675e790000 0x0cf9b9ecebcf2000 0x4789ce660c600000 0x88f139ccc18c0000

def z335 : W := mkw 0x26ef68001f5e0000 0x04dded0003ebc000 0xe7f7c0001f9c0002 0xfcfef80003f38000

def z336 : W := mkw 0x04c8d62b9e718ae5 0x40991ac573ce315c 0xfff9fe7f9ff39fe7 0xffff3fcff3fe73fc

def z337 : W := mkw 0x477fffffe5b7aeed 0xc8effffffcb6f5dd 0xffffffffffffffff 0xffffffffffffffff

def z338 : W := mkw 0x1fdd01d45ac87512 0x03fba03a8b590ea2 0xfffe01fe7fec7f9d 0xffffc03fcffd8ff3

def z339 : W := mkw 0x67ffbdfffb4e0000 0x0cfff7bfff69c000 0x67fffffff38c0007 0xecfffffffe718000

def z340 : W := mkw 0x26ff7a98bfffa629 0x84dfef5317fff4c5 0xf7fffe181fff8603 0xfeffffc303fff0c0

def z341 : W := mkw 0x0000560a84318ae5 0x40000ac15086315c 0x98083e1e0c739fe1 0x130107c3c18e73fc

def z342 : W := mkw 0x1458009402c02500 0x028b0012805804a0 0x9878007e0fe01f85 0xb30f000fc1fc03f0

def z343 : W := mkw 0x0a27f029e51e8a7f 0x8144fe053ca3d14f 0x0007f001e01f807a 0x0000fe003c03f00f

def z344 : W := mkw 0x0180014018005000 0x0030002803000a00 0x478000600c001800 0x88f0000c01800300

def z345 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800000180100066 0x310000003002000c

def z346 : W := mkw 0x0a05d62bc4398af7 0x4140bac57887315e 0x0007fe01e01f807a 0x0000ffc03c03f00f

def z347 : W := mkw 0x119001d418807500 0x0232003a83100ea0 0xef8001fe1c007f84 0xfdf0003fc3800ff0

def z348 : W := mkw 0x4fffbdfff8085012 0x09fff7bfff010a02 0x67fffffff00c601f 0xecfffffffe018c03

def z349 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0x4f81c1e1ec00787c 0x89f0383c3d800f0f

def z350 : W := mkw 0x228542001f7f0000 0x0450a84003efe000 0xf787c0001fff8002 0xfef0f80003fff000

def z351 : W := mkw 0x046a280000000000 0x008d450000000000 0x00783e0000000001 0x000f07c000000000

def z352 : W := mkw 0x0b85c3615c39daf7 0x4170b86c2b873b5e 0xff87c1e1fc7ffffe 0xfff0f83c3f8fffff

def z353 : W := mkw 0x2a27ea21453f0856 0x0544fd4428a7e10a 0x0007fe01e01f807a 0x0000ffc03c03f00f

def z354 : W := mkw 0x0448000000000000 0x0089000000000000 0x47f8000000000001 0xe8ff000000000000

def z355 : W := mkw 0x0b95c1f15c987c56 0x0172b83e2b930f8a 0xfff7c1f9ff9c7e7f 0xfffef83f3ff38fcf

def z356 : W := mkw 0x491095ffe0005856 0x092212bffc000b0a 0x080001ffe000787c 0x0100003ffc000f0f

def z357 : W := mkw 0x147a309ca3c6a729 0x828f46139478d4e5 0x1078301e03e38781 0x020f0603c07c70f0

def z358 : W := mkw 0x0022f62b85378ae5 0x40045ec570a6f15c 0xb87ffe7f9fff9fe7 0xf70fffcff3fff3fc

def z359 : W := mkw 0x0b05816140005856 0x0160b02c28000b0a 0x4f87c1e1e000787e 0xe9f0f83c3c000f0f

def z360 : W := mkw 0x0032209021862408 0x800644120430c481 0xb8760198738c661d 0x770ec0330e718cc3

def z361 : W := mkw 0x00223008a1068229 0x800446011420d045 0xa8063181f01fe07e 0x7500c6303e03fc0f

def z362 : W := mkw 0x155801d402c07500 0x02ab003a80580ea0 0x187801fe03e07f85 0x030f003fc07c0ff0

def z363 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0x08063199e01fe67e 0x0100c6333c03fccf

def z364 : W := mkw 0x10b23098bbc6f729 0x821646131778dee5 0xb8763199ffffffff 0x770ec6333fffffff

def z365 : W := mkw 0x0000000000000000 0x0000000000000000 0x0009fe0000000003 0xa0013fc000000000

def z366 : W := mkw 0x0000100880008221 0x0000020110001044 0x9808307f8c739fe7 0xb301060ff18e73fc

def z367 : W := mkw 0x0000d62b85b7aeed 0xc0001ac570b6f5dd 0xb809fe7f9fffffff 0xb7013fcff3ffffff

def z368 : W := mkw 0x0000000000000000 0x0000000000000000 0x20060180700c6018 0x4400c0300e018c03

def z369 : W := mkw 0x0000000000000000 0x0000000000000000 0x08000181e000607c 0x010000303c000c0f

def z370 : W := mkw 0x0448000002400000 0x0089000000480000 0x1078000003e00001 0x020f0000007c0000

def z371 : W := mkw 0x14d800941ac07500 0x029b001283580ea0 0xb878001e1fe07f81 0x170f0003c3fc0ff0

def z372 : W := mkw 0x00323098a0000000 0x0006461314000000 0xa8763199f01c607f 0x750ec6333e038c0f

def z373 : W := mkw 0x0022200001060000 0x000444000020c000 0x20760000138c0000 0x440ec00002718000

def z374 : W := mkw 0x1458d6bf86f1afe5 0x428b1ad7f0de35fc 0x9879fe7f8ff39fe7 0xb30f3fcff1fe73fc

def z375 : W := mkw 0x0010009020802408 0x8002001204100481 0x0000018060006018 0x000000300c000c03

def z376 : W := mkw 0x27ef6b401f7f5000 0x04fded6803efea00 0xffffffe01ffff807 0xfffffffc03ffff00

def z377 : W := mkw 0x0b85c7635c3958d6 0x4170b8ec6b872b1a 0xef8fcfe7fc7c79fe 0xfdf1f9fcff8f8f3f

def z378 : W := mkw 0x0205000000000000 0x0040a00000000000 0x4787c00000000002 0xe8f0f80000000000

def z379 : W := mkw 0x17dd81f55ac07500 0x02fbb03eab580ea0 0xffffc1ffffe07f87 0xfffff83ffffc0ff0

def z380 : W := mkw 0x477fffffe4310000 0x08effffffc862000 0xd7ffffffec738007 0xfafffffffd8e7000

def z381 : W := mkw 0x0000d62b843108c4 0x40001ac570862118 0x0009fe7f8c601987 0xa0013fcff18c0330

def z382 : W := mkw 0x57fffffffef1ffe5 0x4affffffffde3ffc 0xfffffffffff3ffe7 0xfffffffffffe7ffc

def z383 : W := mkw 0x1448000402400100 0x0289000080480020 0x0008000600600180 0x00010000c00c0030

def z384 : W := mkw 0x06ef28001a400000 0x00dde50003480000 0xf7fffe001fe00003 0xfeffffc003fc0000

def z385 : W := mkw 0x26cd08001a480000 0x04d9a10003490000 0x4780000000000000 0x08f0000000000000

def z386 : W := mkw 0x15c801441a405100 0x02b9002883480a20 0xdf88007e0c601f85 0xbbf1000fc18c03f0

def z387 : W := mkw 0x0180c1611c105844 0x0030182c23820b08 0xef81c1e19c107866 0xfdf0383c33820f0c

def z388 : W := mkw 0x0000420004318ae5 0x400008400086315c 0x0000000000138060 0x000000000002700c

def z389 : W := mkw 0x15c801441a405100 0x02b9002883480a20 0xef8801e61c607984 0xfdf1003cc38c0f30

def z390 : W := mkw 0x00223008a186a629 0x800446011430d4c5 0xb8063001f39fe67a 0x1700c6003e73fccf

def z391 : W := mkw 0x1b85c1615ed87d56 0x0370b82c2bdb0faa 0xff87c1e1fffc7ffe 0xfff0f83c3fff8fff

def z392 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0xb80ffffffc7fffff 0xf701ffffff8fffff

def z393 : W := mkw 0x4ffffdfffd9efe7f 0x89ffffbfffb3dfcf 0xffffffffff9ffe7f 0xfffffffffff3ffcf

def z394 : W := mkw 0x0032b4bba0000000 0x0006569774000000 0x007fffffe0000007 0xe00ffffffc000000

def z395 : W := mkw 0x475d8df740000000 0x08ebb1bee8000000 0x47f9cffe00000005 0xe8ff39ffc0000000

def z396 : W := mkw 0x15c801441a405100 0x02b9002883480a20 0x4780000000000000 0x08f0000000000000

def z397 : W := mkw 0x00101098a186a629 0x800202131430d4c5 0xb8000199f39fe67c 0x170000333e73fccf

def z398 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0xb87e31ffffffffff 0xf70fc63fffffffff

def z399 : W := mkw 0x47ffbdfff8005000 0x08fff7bfff000a00 0xeffffffffc007807 0xfdffffffff800f00

def z400 : W := mkw 0x055895ff80000000 0x00ab12bff0000000 0x47f9ffff80000007 0xe8ff3ffff0000000

def z401 : W := mkw 0x0b85014058085012 0x0170a0280b010a02 0xef8601e07c0c781c 0xfdf0c03c0f818f03

def z402 : W := mkw 0x1fddc1f55ed87d56 0x03fbb83eabdb0faa 0xeff7c1e1ff9c787e 0xfdfef83c3ff38f0f

def z403 : W := mkw 0x0b85c7635c3958d6 0x4170b8ec6b872b1a 0x4789ce660c601980 0x88f139ccc18c0330

def z404 : W := mkw 0x1fddc1f55ed87d56 0x03fbb83eabdb0faa 0xfff9c1fe1fe07f85 0xffff383fc3fc0ff0

def z405 : W := mkw 0x0000060200210080 0x400000c040042010 0x00080e0600600180 0x000101c0c00c0030

def z406 : W := mkw 0x2fefe9615f5e5856 0x05fdfd2c2bebcb0a 0xeff7c1e1ff9c787e 0xfdfef83c3ff38f0f

def z407 : W := mkw 0x15c8d76f9e71dbe5 0x42b91aedf3ce3b7c 0xdf89fe7f8c739fe7 0xbbf13fcff18e73fc

def z408 : W := mkw 0x0032f6bba4318ae5 0x40065ed77486315c 0x987fffffec739fe7 0xf30ffffffd8e73fc

def z409 : W := mkw 0x4f7fbdffe0005856 0x09eff7bffc000b0a 0x4fffffffe000787f 0xe9fffffffc000f0f

def z410 : W := mkw 0x26fffebbbfffaeed 0xc4dfffd777fff5dd 0xffffffffffffffff 0xffffffffffffffff

def z411 : W := mkw 0x028540001c180000 0x0050a80003830000 0xef87c181fc1c607e 0xfdf0f8303f838c0f

def z412 : W := mkw 0x57cd8d675a405100 0x0af9b1aceb480a20 0x4789ce660c601980 0x88f139ccc18c0330

def z413 : W := mkw 0x15fa31dcbbc6f729 0x82bf463b9778dee5 0xfff63199f39fe67f 0x7ffec6333e73fccf

def z414 : W := mkw 0x1100014400005100 0x0220002880000a20 0x0000006600001980 0x0000000cc0000330

def z415 : W := mkw 0x466fbc2be0000000 0x08cdf7857c000000 0x47fffe01e0000003 0xe8ffffc03c000000

def z416 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0x4787c061ec1c187a 0x88f0f80c3d83830f

def z417 : W := mkw 0x0000420005b7aeed 0xc000084000b6f5dd 0xb80000001ffffff8 0x1700000003ffffff

def z418 : W := mkw 0x0032b4bba186aeed 0xc00656977430d5dd 0xb87631fff39fffff 0x770ec63ffe73ffff

def z419 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0xfff001801fe07f80 0x5ffe003003fc0ff0

def z420 : W := mkw 0x0337b1f9e0000000 0x0066f63f3c000000 0x47f7f1f9e0000007 0xe8fefe3f3c000000

def z421 : W := mkw 0x0000000000000000 0x0000000000000000 0xb070000013800001 0x760e000002700000

def z422 : W := mkw 0x0000c623043108c4 0x400018c460862118 0x9809ce7e0c601f85 0xb30139cfc18c03f0

def z423 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0xb87031981383e605 0x770e063302707cc0

def z424 : W := mkw 0x04ea20001b460000 0x009d44000368c000 0xf7fe30001fff8003 0xfeffc60003fff000

def z425 : W := mkw 0x05d801d41a400000 0x00bb003a83480000 0xf7f801fe1fe00005 0xfeff003fc3fc0000

def z426 : W := mkw 0x108000001bc6f729 0x821000000378dee5 0xb80000001ffffff8 0x1700000003ffffff

def z427 : W := mkw 0x0000c02104100844 0x0000180420820108 0x9809c07f8c701fe7 0xb301380ff18e03fc

def z428 : W := mkw 0x3fffebf55fff7d56 0x07fffd7eabffefaa 0xffffffffffffffff 0xffffffffffffffff

def z429 : W := mkw 0x0205802140000000 0x0040b00428000000 0x0007c001e0000002 0x0000f8003c000000

def z430 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000300000138003 0x3200060000027000

def z431 : W := mkw 0x0b85d56bdc18daf7 0x4170baad7b831b5e 0xef87c1fffc1c7ffe 0xfdf0f83fff838fff

def z432 : W := mkw 0x0100014000005000 0x0020002800000a00 0x080001e000007804 0x0100003c00000f00

def z433 : W := mkw 0x0000000000000000 0x0000000000000000 0x900800000c600001 0xb2010000018c0000

def z434 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x0009fe7f80138067 0xa0013fcff002700c

def z435 : W := mkw 0x246a3e0a836782a1 0x448d47c1506cf054 0x10783e1e03e38781 0x020f07c3c07c70f0

def z436 : W := mkw 0x447a3e9ea02182a1 0x488f47d3d4043054 0x10783e1e00638781 0x020f07c3c00c70f0

def z437 : W := mkw 0x0b85c1615d9efe7f 0x8170b82c2bb3dfcf 0xff87c1e1ff9ffe7e 0xfff0f83c3ff3ffcf

def z438 : W := mkw 0x0548014400000000 0x00a9002880000000 0x4788006600000000 0x88f1000cc0000000

def z439 : W := mkw 0x057a31dca186a629 0x80af463b9430d4c5 0xfffe31fff39fe67f 0xffffc63ffe73fccf

def z440 : W := mkw 0x0000c02104100844 0x0000180420820108 0x0001c0600c001800 0x8000380c01800300

def z441 : W := mkw 0x26cdce231e7908c4 0x44d9b9c463cf2118 0x4789ce660c601980 0x88f139ccc18c0330

def z442 : W := mkw 0x155801d400807500 0x02ab003a80100ea0 0x4ff801fe00007f85 0xe9ff003fc0000ff0

def z443 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xfffffe7e1fff9f87 0xffffffcfc3fff3f0

def z444 : W := mkw 0x2eefea215f7f0856 0x05ddfd442befe10a 0xf7fffe01ffff807b 0xfeffffc03ffff00f

def z445 : W := mkw 0x17dd41d41ed87500 0x02fba83a83db0ea0 0xffffc1fe1ffc7f87 0xfffff83fc3ff8ff0

def z446 : W := mkw 0x77ffffffffff7500 0x0effffffffffeea0 0xffffffffffffff87 0xfffffffffffffff0

def z447 : W := mkw 0x003220902186a629 0x800644120430d4c5 0xb8760180739fe678 0x570ec0300e73fccf

def z448 : W := mkw 0x0032f0b9a596ae6d 0x80065e1734b2d5cd 0xb877f1f9ff9ffe7f 0xf70efe3f3ff3ffcf

def z449 : W := mkw 0x208000001b4e0000 0x041000000369c000 0x20000000138c0000 0x0400000002718000

def z450 : W := mkw 0x00323098a0000000 0x0006461314000000 0x0070301800000001 0x000e060300000000

def z451 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x9801fe1980138667 0x33003fc3300270cc

def z452 : W := mkw 0x2227fe2b853f8ae5 0x4444ffc570a7f15c 0x980ffe7f8c7f9fe7 0xb301ffcff18ff3fc

def z453 : W := mkw 0x4227fe2be4318ae5 0x4844ffc57c86315c 0x980ffe7fec739fe7 0xb301ffcffd8e73fc

def z454 : W := mkw 0x0022200001060000 0x000444000020c000 0x1070300003838001 0x020e060000707000

def z455 : W := mkw 0x37ef6b441f7f5100 0x06fded6883efea20 0xf7fffe661fff9983 0xfeffffccc3fff330

def z456 : W := mkw 0x0000c22104310844 0x0000184420862108 0x9809fe618c739867 0xb3013fcc318e730c

def z457 : W := mkw 0x15d8c7f71ef17dc4 0x42bb18fee3de2fb8 0xfff9cffe1fe07f85 0xffff39ffc3fc0ff0

def z458 : W := mkw 0x0b85816158085856 0x0170b02c2b010b0a 0x6f8601e1f00c787c 0x4df0c03c3e018f0f

def z459 : W := mkw 0x208042001fffa629 0x8410084003fff4c5 0xb80000001fffe678 0x1700000003fffccf

def z460 : W := mkw 0x00101098a080a629 0x80020213141014c5 0xa8060199f01c667e 0x7500c0333e038ccf

def z461 : W := mkw 0x26ff28903bce2408 0x84dfe5120779c481 0x67f60180738c6018 0x4cfec0300e718c03

def z462 : W := mkw 0x26cd4a001f7f0000 0x04d9a94003efe000 0xf789ce001fff8000 0x9ef139c003fff000

def z463 : W := mkw 0x0000d42b84108ae5 0x40001a857082115c 0x8801c07f8c101fe6 0xb100380ff18203fc

def z464 : W := mkw 0x0980c1615c185856 0x0130182c2b830b0a 0xa80001e1fc1c787c 0x1500003c3f838f0f

def z465 : W := mkw 0x15faf7ffbff7ffed 0xc2bf5efff7fefffd 0xffffffffffffffff 0xffffffffffffffff

def z466 : W := mkw 0x455895ffe0000000 0x08ab12bffc000000 0x47f801ffe0000005 0xe8ff003ffc000000

def z467 : W := mkw 0x067f3898a186a629 0x80cfe7131430d4c5 0xffffff99f39fe67f 0xfffffff33e73fccf

def z468 : W := mkw 0x20004200053f0000 0x0400084000a7e000 0x00000000001f8000 0x000000000003f000

def z469 : W := mkw 0x0000100880000000 0x0000020110000000 0x0000301980000007 0x2000060330000000

def z470 : W := mkw 0x0032209021862408 0x800644120430c481 0xb0763180739fe01b 0x760ec6300e73fc03

def z471 : W := mkw 0x475d9dffe0000000 0x08ebb3bffc000000 0x4789cfffe0000004 0x88f139fffc000000

def z472 : W := mkw 0x4100856740000000 0x082010ace8000000 0x0000006600000000 0x0000000cc0000000

def z473 : W := mkw 0x0032209021862408 0x800644120430c481 0x0070000003800000 0x000e000000700000

def z474 : W := mkw 0x474dcf67443108c4 0x48e9b9ece8862118 0x4789ce660c601980 0x88f139ccc18c0330

def z475 : W := mkw 0x22377a98a5bfa629 0x8446ef5314b7f4c5 0xb877ff99f39fe67f 0x770efff33e73fccf

def z476 : W := mkw 0x4237bcbbe186a629 0x8846f7977c30d4c5 0xb877ff99f39fe67f 0x770efff33e73fccf

def z477 : W := mkw 0x1fcdc1655e585956 0x03f9b82cabcb0b2a 0xef8fc1e7fc7c79fe 0xfdf1f83cff8f8f3f

def z478 : W := mkw 0x35fa2bd41be77500 0x06bf457a837ceea0 0xfff83ffe1fe3ff85 0xffff07ffc3fc7ff0

def z479 : W := mkw 0x0a85c0215c180856 0x0150b8042b83010a 0xe787c001fc1c007a 0xfcf0f8003f83800f

def z480 : W := mkw 0x477f39dce0000000 0x08efe73b9c000000 0x47f63199e0000007 0x68fec6333c000000

def z481 : W := mkw 0x477fa9f560000000 0x08eff53eac000000 0x47f7c1e1e0000006 0xe8fef83c3c000000

def z482 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xf7f600001fff8000 0x5efec00003fff000

def z483 : W := mkw 0x26ef6a001f7f8ae5 0x44dded4003eff15c 0xfffffe001fff9fe3 0xffffffc003fff3fc

def z484 : W := mkw 0x098041401c185856 0x0130082803830b0a 0xef8001e01c1c787c 0xfdf0003c03838f0f

def z485 : W := mkw 0x0000400004100000 0x0000080000820000 0x8001c0000c100002 0xb000380001820000

def z486 : W := mkw 0x0000942b80000000 0x0000128570000000 0x0001fe0180000002 0x00003fc030000000

def z487 : W := mkw 0x57dd8df75ac07500 0x0afbb1beeb580ea0 0xfff9cffe1fe07f85 0xffff39ffc3fc0ff0

def z488 : W := mkw 0x0000000000000000 0x0000000000000000 0x0008007e00000005 0xa001000fc0000000

def z489 : W := mkw 0x0932b1f9e186fe7f 0x8126563f3c30dfcf 0xb87631f9f39ffe7f 0x770ec63f3e73ffcf

def z490 : W := mkw 0x0b05c16144185856 0x0160b82c28830b0a 0x0807c1e1e01c787e 0x0100f83c3c038f0f

def z491 : W := mkw 0x14c800001ac07500 0x0299000003580ea0 0xfff800001fe07f81 0xffff000003fc0ff0

def z492 : W := mkw 0x26effe2b9f7f0000 0x04ddffc573efe000 0xf7fffe7f9fff8007 0xfeffffcff3fff000

def z493 : W := mkw 0x4227280060000000 0x0844e5000c000000 0x0006000060000000 0x0000c0000c000000

def z494 : W := mkw 0x00101098a0000000 0x0002021314000000 0x00000199e0000004 0x000000333c000000

def z495 : W := mkw 0x0180014018005000 0x0030002803000a00 0xff8801fe1c607f85 0xfff1003fc38c0ff0

def z496 : W := mkw 0x2ffffbf9fffffe7f 0x85ffff7f3fffffcf 0xfffffff9fffffe7f 0xffffffff3fffffcf

def z497 : W := mkw 0x0385c1615c180000 0x0070b82c2b830000 0xe787c1e1fc1c0006 0xfcf0f83c3f838000

def z498 : W := mkw 0x26ef28001b4e0000 0x04dde5000369c000 0x67fffe00138c0003 0xecffffc002718000

def z499 : W := mkw 0x000000000186a629 0x800000000030d4c5 0x1000000003838600 0x02000000007070c0

def z500 : W := mkw 0x0285c0211c180844 0x0050b80423830108 0xef87c0619c1c1866 0xfdf0f80c3383830c

def z501 : W := mkw 0x0010d6bb84b1aee5 0x40021ad7709635dc 0xb879ffff9ff3ffe7 0xf70f3ffff3fe7ffc

def z502 : W := mkw 0x37dd4bd41ef97500 0x06fba97a83df2ea0 0xfff9cffe1fe07f85 0xffff39ffc3fc0ff0

def z503 : W := mkw 0x67fffffffe790000 0x0cffffffffcf2000 0x47ffffffec600007 0xe8fffffffd8c0000

def z504 : W := mkw 0x2b85c3615f7f5856 0x0570b86c2befeb0a 0xff87c1e1fffff87e 0xfff0f83c3fffff0f

def z505 : W := mkw 0x066f6a0004310000 0x00cded4000862000 0xd7fffe000c738003 0xfaffffc0018e7000

def z506 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0x30763198738fe619 0x460ec6330e71fcc3

def z507 : W := mkw 0x2fef6b405f7f5012 0x05fded680befea02 0xf7ffff807fffe01b 0xfefffff00ffffc03

def z508 : W := mkw 0x22276a00053f0000 0x0444ed4000a7e000 0x900ffe000c7f8003 0xb201ffc0018ff000

def z509 : W := mkw 0x0a05000040080012 0x0140a00008010002 0x00060000600c0018 0x0000c0000c018003

def z510 : W := mkw 0x246a2a0003670000 0x048d4540006ce000 0xb07e3e0013ff8003 0x760fc7c0027ff000

def z511 : W := mkw 0x26ff7a98bf7f0000 0x04dfef5317efe000 0xf7ffff99ffff8007 0xfefffff33ffff000

def z512 : W := mkw 0x0010009000802400 0x0002001200100480 0x2070018013806000 0x440e003002700c00

def z513 : W := mkw 0x15fa31dcbac07500 0x02bf463b97580ea0 0xfffe31ffffe07f87 0xffffc63ffffc0ff0

def z514 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0xb8703018139fe679 0x170e06030273fccf

def z515 : W := mkw 0x0000962b802182a1 0x400012c570043054 0x1009fe7f80638787 0xa2013fcff00c70f0

def z516 : W := mkw 0x1458009402c02500 0x028b0012805804a0 0x0070000003800000 0x000e000000700000

def z517 : W := mkw 0x0b8541405c185856 0x0170a8280b830b0a 0xef8601807c1c7878 0x5df0c0300f838f0f

def z518 : W := mkw 0x1fddd7ffdef9fff7 0x43fbbafffbdf3ffe 0xffffffffffffffff 0xffffffffffffffff

def z519 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x47f601ffe0000004 0x48fec03ffc000000

def z520 : W := mkw 0x266f6a00053f0000 0x04cded4000a7e000 0x47fffe00001f8003 0xe8ffffc00003f000

def z521 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0xeff001e01f807804 0xfdfe003c03f00f00

def z522 : W := mkw 0x00323098a0008221 0x0006461314001044 0x98763199e0138667 0x730ec6333c0270cc

def z523 : W := mkw 0x04d800901ac02400 0x009b001203580480 0xfff801981fe06605 0xffff003303fc0cc0

def z524 : W := mkw 0x44480c0600000000 0x08890180c0000000 0x00080e0600000000 0x000101c0c0000000

def z525 : W := mkw 0x0b85d169dc18da77 0x0170ba2d3b831b4e 0xff87f1f9fc1ffe7f 0xfff0fe3f3f83ffcf

def z526 : W := mkw 0x00101098a080a629 0x80020213141014c5 0x0000001800000600 0x00000003000000c0

def z527 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0x67ffce001fec0000 0xccfff9c003fd8000

def z528 : W := mkw 0x0bb7e1f17d9e7c5e 0x8176fc3e2fb3cf8b 0xeff7c1e1ff9c787e 0xfdfef83c3ff38f0f

def z529 : W := mkw 0x0000400004100844 0x0000080000820108 0x880000000c101860 0x110000000182030c

def z530 : W := mkw 0x00101098a080a629 0x80020213141014c5 0x98003199e013e67f 0x330006333c027ccf

def z531 : W := mkw 0x26efee231f7f08c4 0x44ddfdc463efe118 0xf7fffe661fff9983 0xfeffffccc3fff330

def z532 : W := mkw 0x15d895ff9ac0ffe5 0x42bb12bff3581ffc 0xfff801ff9fe07fe5 0xffff003ff3fc0ffc

def z533 : W := mkw 0x36ef6a001fff7500 0x06dded4003ffeea0 0xfffffe001fffff83 0xffffffc003fffff0

def z534 : W := mkw 0x0010009000802400 0x0002001200100480 0x1070001803800601 0x020e0003007000c0

def z535 : W := mkw 0x67ffffffff7f8ae5 0x4cffffffffeff15c 0xffffffffffff9fe7 0xfffffffffffff3fc

def z536 : W := mkw 0x000010088186a629 0x800002011030d4c5 0xb8003019939fe67f 0x370006033273fccf

def z537 : W := mkw 0x208042001f7f0000 0x0410084003efe000 0xb009fe001fff8003 0xb6013fc003fff000

def z538 : W := mkw 0x0000520884318ae5 0x40000a411086315c 0x980030198c739fe7 0x33000603318e73fc

def z539 : W := mkw 0x4227bc2be0000000 0x0844f7857c000000 0x000ffe7fe0000007 0xa001ffcffc000000

def z540 : W := mkw 0x0000000000000000 0x0000000000000000 0x880000600c001804 0xb100000c01800300

def z541 : W := mkw 0x00223008a1068229 0x800446011420d045 0x98063019e01f867f 0x3300c6033c03f0cf

def z542 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x0009fe678c7399e2 0x80013fccf18e733c

def z543 : W := mkw 0x0a05c02144180856 0x0140b8042883010a 0xa807c181f01c607e 0x7500f8303e038c0f

def z544 : W := mkw 0x0900014040005012 0x0120002808000a02 0x0000018060006018 0x000000300c000c03

def z545 : W := mkw 0x40223c0aa0000000 0x0804478154000000 0x00003e0000000000 0x000007c000000000

def z546 : W := mkw 0x02b77098bd9ea629 0x8056ee1317b3d4c5 0xfff7f199ff9fe67f 0xfffefe333ff3fccf

def z547 : W := mkw 0x4ffffffffc39daf7 0x49ffffffff873b5e 0xfffffffffc7fffff 0xffffffffff8fffff

def z548 : W := mkw 0x0032209021862408 0x800644120430c481 0xa8760181f39c607e 0x750ec0303e738c0f

def z549 : W := mkw 0x0fcdc1615e585856 0x01f9b82c2bcb0b0a 0xffffc1e1fffc787f 0xfffff83c3fff8f0f

def z550 : W := mkw 0x477fbfffe02182a1 0x48eff7fffc043054 0x57ffffffe0638787 0xeafffffffc0c70f0

def z551 : W := mkw 0x22a76a001d3f0000 0x0454ed4003a7e000 0xe787fe001c1f8002 0xfcf0ffc00383f000

def z552 : W := mkw 0x67ff6bd47f7f0000 0x0cffed7a8fefe000 0xf7ffff807fff8003 0xfefffff00ffff000

def z553 : W := mkw 0x0800000000005856 0x0100000000000b0a 0x0800000000007878 0x0100000000000f0f

def z554 : W := mkw 0x208042001f7f8ae5 0x4410084003eff15c 0xb80000001fff9fe0 0x1700000003fff3fc

def z555 : W := mkw 0x088040001c185856 0x0110080003830b0a 0xa8060181fc1c787e 0x7500c0303f838f0f

def z556 : W := mkw 0x111001d400807500 0x0222003a80100ea0 0x980801fe0c607f85 0xb301003fc18c0ff0

def z557 : W := mkw 0x1000000000807500 0x0200000000100ea0 0x0800000000007f80 0x0100000000000ff0

def z558 : W := mkw 0x1080d62b9ef1ffe5 0x42101ac573de3ffc 0xb809fe7f9ff3ffe7 0xb7013fcff3fe7ffc

def z559 : W := mkw 0x6227fe2be53f0000 0x0c44ffc57ca7e000 0x0007fe01e01f8002 0x0000ffc03c03f000

def z560 : W := mkw 0x0022f62ba5378aed 0xc0045ec574a6f15d 0x0007fe01e01f807a 0x0000ffc03c03f00f

def z561 : W := mkw 0x15c8c7671e7159c4 0x42b918ece3ce2b38 0x4789ce660c601980 0x88f139ccc18c0330

def z562 : W := mkw 0x055801d400000000 0x00ab003a80000000 0x47f0018000000000 0x48fe003000000000

def z563 : W := mkw 0x00001008a0008229 0x8000020114001045 0x00000001e0000078 0x000000003c00000f

def z564 : W := mkw 0x47fffdfffc180000 0x08ffffbfff830000 0xe7fffffffc1c0007 0xfcffffffff838000

def z565 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x9801fe018c739fe2 0x13003fc0318e73fc

def z566 : W := mkw 0x002220000186a629 0x800444000030d4c5 0xb8763000139fe67b 0x770ec6000273fccf

def z567 : W := mkw 0x0000520884318221 0x00000a4110863044 0x9809fe198c738667 0xb3013fc3318e70cc

def z568 : W := mkw 0x0080000018000000 0x0010000003000000 0xe78000001c000000 0xfcf0000003800000

def z569 : W := mkw 0x0000962b80218ae5 0x400012c57004315c 0x18083e7f80639fe5 0x030107cff00c73fc

def z570 : W := mkw 0x0000420004318ae5 0x400008400086315c 0x9808007e0c739fe5 0xb301000fc18e73fc

def z571 : W := mkw 0x0880000018085012 0x0110000003010a02 0x20000000100c6018 0x0400000002018c03

def z572 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0x478ffe000c7f8002 0x88f1ffc0018ff000

def z573 : W := mkw 0x0000d62b84310000 0x00001ac570862000 0x9009fe7f8c738007 0xb2013fcff18e7000

def z574 : W := mkw 0x4f7ffdffe4180856 0x09efffbffc83010a 0x47ffffffe01c007f 0xe8fffffffc03800f

def z575 : W := mkw 0x0000d42b84100844 0x00001a8570820108 0x8809fe7f8c101867 0xb1013fcff182030c

def z576 : W := mkw 0x57ffbdfffa405100 0x0afff7bfff480a20 0x47ffffffec601987 0xe8fffffffd8c0330

def z577 : W := mkw 0x15d817de9ae1f7a1 0x42bb02fbd35c3ef4 0xfff83ffe1fe3ff85 0xffff07ffc3fc7ff0

def z578 : W := mkw 0x457a3ddea0000000 0x08af47bbd4000000 0x47f83ffe00000005 0xe8ff07ffc0000000

def z579 : W := mkw 0x1110d7ff84b1ffe5 0x42221afff0963ffc 0x9809ffff8c73ffe7 0xb3013ffff18e7ffc

def z580 : W := mkw 0x088042001c39daf7 0x4110084003873b5e 0xb80000001c7ffff8 0x17000000038fffff

def z581 : W := mkw 0x0000c62304318ae5 0x400018c46086315c 0x9809ce660c739fe0 0x930139ccc18e73fc

def z582 : W := mkw 0x188040001ed87d56 0x0310080003db0faa 0xb80000001ffc7ff8 0x1700000003ff8fff

def z583 : W := mkw 0x011001d400000000 0x0022003a80000000 0x000001fe00000004 0x0000003fc0000000

def z584 : W := mkw 0x00323098a1060000 0x000646131420c000 0xb0763199f39f8007 0x760ec6333e73f000

def z585 : W := mkw 0x0800400004180856 0x010008000083010a 0x00000000001c0078 0x000000000003800f

def z586 : W := mkw 0x431595ffe0000000 0x0862b2bffc000000 0x4787c1ffe0000006 0xe8f0f83ffc000000

def z587 : W := mkw 0x0100014000000000 0x0020002800000000 0x478001e000000004 0xe8f0003c00000000

def z588 : W := mkw 0x0b85014058085012 0x0170a0280b010a02 0x4780000000000000 0x08f0000000000000

def z589 : W := mkw 0x0000140a800082a1 0x4000028150001054 0x0000001e00000780 0x00000003c00000f0

def z590 : W := mkw 0x0032f6bba5b7aeed 0xc0065ed774b6f5dd 0x9879fe7f8ff39fe7 0xb30f3fcff1fe73fc

def z591 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0x28760199f38c667c 0x450ec0333e718ccf

def z592 : W := mkw 0x15d843d41ef1ffe5 0x42bb087a83de3ffc 0xfff801fe1ff3ffe5 0xffff003fc3fe7ffc

def z593 : W := mkw 0x4110d7ffe4318ae5 0x48221afffc86315c 0x9809ffffec739fe7 0xb3013ffffd8e73fc

def z594 : W := mkw 0x0000000000000000 0x0000000000000000 0x000800660c601980 0x8001000cc18c0330

def z595 : W := mkw 0x000000000080a629 0x80000000001014c5 0x0800000000006678 0x0100000000000ccf

def z596 : W := mkw 0x67efef675f7f0000 0x0cfdfdecebefe000 0xf7fffe661fff8003 0xfeffffccc3fff000

def z597 : W := mkw 0x0fddc1f55c185856 0x01fbb83eab830b0a 0xefffc1fffc1c787f 0xfdfff83fff838f0f

def z598 : W := mkw 0x447a3c9ea0000000 0x088f4793d4000000 0x007e3f9fe0000007 0x600fc7f3fc000000

def z599 : W := mkw 0x0a05d62bc4398af7 0x4140bac57887315e 0x980ffe7fec7f9fff 0xb301ffcffd8ff3ff

def z600 : W := mkw 0x55fa3ddebac07500 0x0abf47bbd7580ea0 0xfff83ffe1fe07f85 0xffff07ffc3fc0ff0

def z601 : W := mkw 0x24480a0002610000 0x04890140004c2000 0x00080e0000600000 0x000101c0000c0000

def z602 : W := mkw 0x347a2a9403e72500 0x068f4552807ce4a0 0x10783e1e03e38781 0x020f07c3c07c70f0

def z603 : W := mkw 0x1458009402c02500 0x028b0012805804a0 0xb878019e13e06785 0x770f0033c27c0cf0

def z604 : W := mkw 0x477ffdffe4100844 0x08efffbffc820108 0xcfffffffec101867 0xf9fffffffd82030c

def z605 : W := mkw 0x477fffffe4318ae5 0x48effffffc86315c 0x47ffffffe0138067 0xe8fffffffc02700c

def z606 : W := mkw 0x0000160a802182a1 0x400002c150043054 0x98083e1f807387e7 0x330107c3f00e70fc

def z607 : W := mkw 0x0010009000802400 0x0002001200100480 0xb87801fe1fe07f85 0xf70f003fc3fc0ff0

def z608 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0xb0763018139f8603 0x760ec6030273f0c0

def z609 : W := mkw 0x00327298a5b7a629 0x80064e5314b6f4c5 0xb87fff99ffffe67f 0xf70ffff33ffffccf

def z610 : W := mkw 0x00323098a1862408 0x800646131430c481 0x20763199f38c601f 0x640ec6333e718c03

def z611 : W := mkw 0x088040001d9efe7f 0x8110080003b3dfcf 0xb80000001f9ffe78 0x1700000003f3ffcf

def z612 : W := mkw 0x26ef6a001fffa629 0x84dded4003fff4c5 0xfffffe001fffe67b 0xffffffc003fffccf

def z613 : W := mkw 0x0010009000802400 0x0002001200100480 0xb8760199f39c667f 0x770ec0333e738ccf

def z614 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0x10763199e3838607 0x620ec6333c7070c0

def z615 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x0801fe7f80139fe6 0x01003fcff00273fc

def z616 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0xfff0019813806605 0x7ffe003302700cc0

def z617 : W := mkw 0x1458169e82e1a7a1 0x428b02d3d05c34f4 0x10783e1e03e38781 0x020f07c3c07c70f0

def z618 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x0809ce7f8c601fe4 0x810139cff18c03fc

def z619 : W := mkw 0x0000160a802182a1 0x400002c150043054 0x00003e0000038000 0x000007c000007000

def z620 : W := mkw 0x0bb731d8f98ef63b 0x8176e63b1f31dec7 0xfff63199f39fe67f 0x7ffec6333e73fccf

def z621 : W := mkw 0x2fefeb615f7f5856 0x05fdfd6c2befeb0a 0xf7fffe601fff9803 0xfeffffcc03fff300

def z622 : W := mkw 0x4227bc2be1068229 0x8844f7857c20d045 0x0007fe01e01f807a 0x0000ffc03c03f00f

def z623 : W := mkw 0x04fa3098bbc6a629 0x809f46131778d4c5 0xfffe3199ffffe67f 0xffffc6333ffffccf

def z624 : W := mkw 0x0000100880008221 0x0000020110001044 0x0000300180138062 0x000006003002700c

def z625 : W := mkw 0x457abdffe0000000 0x08af57bffc000000 0x00783fffe0000005 0x000f07fffc000000

def z626 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0x67f801e61fe07980 0xccff003cc3fc0f30

def z627 : W := mkw 0x26ef2a001b6f0000 0x04dde540036de000 0x77fe3e0013ef8001 0x4effc7c0027df000

def z628 : W := mkw 0x00000200002182a1 0x4000004000043054 0x1000000000638780 0x02000000000c70f0

def z629 : W := mkw 0x0305014040000000 0x0060a02808000000 0x4786018060000000 0x48f0c0300c000000

def z630 : W := mkw 0x0000000000008ae5 0x400000000000115c 0x0800000000001fe0 0x01000000000003fc

def z631 : W := mkw 0x0b85816158085012 0x0170b02c2b010a02 0x6787c1e1f00c601e 0xecf0f83c3e018c03

def z632 : W := mkw 0x0bb7f7fbfdbffeff 0xc176feff7fb7ffdf 0xffffffffffffffff 0xffffffffffffffff

def z633 : W := mkw 0x00008423000008c4 0x4000108460000118 0x0000006600001980 0x0000000cc0000330

def z634 : W := mkw 0x511095ffe0807500 0x0a2212bffc100ea0 0x080001ffe0007f84 0x0100003ffc000ff0

def z635 : W := mkw 0x111001d400807500 0x0222003a80100ea0 0xb87001fe13807f85 0x770e003fc2700ff0

def z636 : W := mkw 0x0900d76bc431daf7 0x41201aed78863b5e 0x9809ffffec73ffff 0xb3013ffffd8e7fff

def z637 : W := mkw 0x26cd4a001e790000 0x04d9a94003cf2000 0xe78fce001c7c0002 0xfcf1f9c0038f8000

def z638 : W := mkw 0x0022620005370000 0x00044c4000a6e000 0xb07ffe001fff8003 0xf60fffc003fff000

def z639 : W := mkw 0x0900816140005856 0x0120102c28000b0a 0x0000006000001800 0x0000000c00000300

def z640 : W := mkw 0x113231dca186f729 0x8226463b9430dee5 0xb87631fff39fffff 0x770ec63ffe73ffff

def z641 : W := mkw 0x411001d460000000 0x0822003a8c000000 0x0000018060000000 0x000000300c000000

def z642 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0xf7f801801fe06001 0xfeff003003fc0c00

def z643 : W := mkw 0x0b05c16144180856 0x0160b82c2883010a 0x4787c1e1e01c007e 0xe8f0f83c3c03800f

def z644 : W := mkw 0x0000000000000000 0x0000000000000000 0xa8000000101c6078 0x1500000002038c0f

def z645 : W := mkw 0x0558d7ff84318ae5 0x40ab1afff086315c 0xdff9ffff8c739fe7 0xfbff3ffff18e73fc

def z646 : W := mkw 0x0000000000000000 0x0000000000000000 0x9800001800000605 0x33000003000000c0

def z647 : W := mkw 0x2fefff6bdf7fdaf7 0x45fdffed7beffb5e 0xffffffffffffffff 0xffffffffffffffff

def z648 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x1009fe1f807387e3 0x02013fc3f00e70fc

def z649 : W := mkw 0x4227fe2be4318ae5 0x4844ffc57c86315c 0x0007fe01e0138062 0x0000ffc03c02700c

def z650 : W := mkw 0x24ea6a001f7f0000 0x049d4d4003efe000 0xb0783e001fff8001 0x160f07c003fff000

def z651 : W := mkw 0x37cd4b441e795100 0x06f9a96883cf2a20 0x4789ce660c601980 0x88f139ccc18c0330

def z652 : W := mkw 0x0000942b80000000 0x0000128570000000 0x9809fe7f8c601f87 0xb3013fcff18c03f0

def z653 : W := mkw 0x66effe2bff7f0000 0x0cddffc57fefe000 0xf7fffe01ffff8003 0xfeffffc03ffff000

def z654 : W := mkw 0x26ef7e0a9f7f82a1 0x44ddefc153eff054 0xf7fffe1e1fff8783 0xfeffffc3c3fff0f0

def z655 : W := mkw 0x2ba7eb615d3f5856 0x0574fd6c2ba7eb0a 0xef87ffe1fc1ff87e 0xfdf0fffc3f83ff0f

def z656 : W := mkw 0x0000942b80008ae5 0x400012857000115c 0x0000000180000060 0x000000003000000c

def z657 : W := mkw 0x477f39dce186a629 0x88efe73b9c30d4c5 0xfff63199f39fe67f 0x7ffec6333e73fccf

def z658 : W := mkw 0x0000000000000000 0x0000000000000000 0x00060181e0000006 0x6000c0303c000000

def z659 : W := mkw 0x677fffffe53f0000 0x0ceffffffca7e000 0x47ffffffe01f8007 0xe8fffffffc03f000

def z660 : W := mkw 0x001010988080a621 0x00020213101014c4 0xb87031999393e667 0x770e063332727ccc

def z661 : W := mkw 0x24ea2a001b670000 0x049d4540036ce000 0xf7f83e001fe38001 0xfeff07c003fc7000

def z662 : W := mkw 0x0010009000000000 0x0002001200000000 0x0070019800000005 0x600e003300000000

def z663 : W := mkw 0x20222a0001270000 0x040445400024e000 0x00003e0000038000 0x000007c000007000

def z664 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0x18703199e383e67d 0x030e06333c707ccf

def z665 : W := mkw 0x0000c02104100844 0x0000180420820108 0xa807c1e1fc1c787e 0xf500f83c3f838f0f

def z666 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0x4f8801fe0c607f84 0x89f1003fc18c0ff0

def z667 : W := mkw 0x06cd40001e580000 0x00d9a80003cb0000 0xf7ffc0001ffc0003 0xfefff80003ff8000

def z668 : W := mkw 0x057a31dca0000000 0x00af463b94000000 0x47fe31ffe0000007 0xe8ffc63ffc000000

def z669 : W := mkw 0x477f29d460000000 0x08efe53a8c000000 0x47fe01fe60000005 0xe8ffc03fcc000000

def z670 : W := mkw 0x246afe2b87778ae5 0x448d5fc570eef15c 0x9879fe7f8ff39fe7 0xb30f3fcff1fe73fc

def z671 : W := mkw 0x0022300881068221 0x000446011020d044 0xb8763019939f8667 0x770ec6033273f0cc

def z672 : W := mkw 0x37ff29d41bce7500 0x06ffe53a8379cea0 0xfffe01fe1fec7f85 0xffffc03fc3fd8ff0

def z673 : W := mkw 0x019001d018807400 0x0032003a03100e80 0xfff001f81f807e05 0xfffe003f03f00fc0

def z674 : W := mkw 0x15fa21d43bc67508 0x82bf443a8778cea1 0x67f60180738c6018 0x4cfec0300e718c03

def z675 : W := mkw 0x0a37f0b9e59eae7f 0x8146fe173cb3d5cf 0xb877f199f39fe67f 0x770efe333e73fccf

def z676 : W := mkw 0x001094bba080aeed 0xc0021297741015dd 0x080001ffe0007ffc 0x0100003ffc000fff

def z677 : W := mkw 0x22276a00053f0000 0x0444ed4000a7e000 0xb077fe00139f8003 0x760effc00273f000

def z678 : W := mkw 0x108000001ac07500 0x0210000003580ea0 0xb808007e1fe07f85 0xb701000fc3fc0ff0

def z679 : W := mkw 0x467fbcbfe0000000 0x08cff797fc000000 0x007ffe1fe0000003 0x000fffc3fc000000

def z680 : W := mkw 0x0b8541405c185012 0x0170a8280b830a02 0xe787c1807c1c601a 0xfcf0f8300f838c03

def z681 : W := mkw 0x411095ffe0000000 0x082212bffc000000 0x0009ffffe0000007 0xa0013ffffc000000

def z682 : W := mkw 0x091091f9e080fe7f 0x8122123f3c101fcf 0x080001f9e0007e7c 0x0100003f3c000fcf

def z683 : W := mkw 0x4132b5ffe0000000 0x082656bffc000000 0x007631ffe0000007 0x600ec63ffc000000

def z684 : W := mkw 0x4ba7fd6bfc185856 0x0974ffad7f830b0a 0xef87ffe1fc1c787e 0xfdf0fffc3f838f0f

def z685 : W := mkw 0x37ff6bd41fff7500 0x06ffed7a83ffeea0 0xf7ffff801fffe003 0xfefffff003fffc00

def z686 : W := mkw 0x108000001ac07500 0x0210000003580ea0 0x2000000013806000 0x0400000002700c00

def z687 : W := mkw 0x2fcdcb615e795856 0x05f9b96c2bcf2b0a 0xef8fcfe1fc7c787e 0xfdf1f9fc3f8f8f0f

def z688 : W := mkw 0x08b27098bd9efe7f 0x81164e1317b3dfcf 0xb8763199ff9ffe7f 0x770ec6333ff3ffcf

def z689 : W := mkw 0x028542001c390000 0x0050a84003872000 0xf78ffe001c7f8003 0xfef1ffc0038ff000

def z690 : W := mkw 0x0000140a80000000 0x0000028150000000 0x00083e1e00000001 0x000107c3c0000000

def z691 : W := mkw 0x66ff7e9ebf7f0000 0x0cdfefd3d7efe000 0xf7fffe1e1fff8003 0xfeffffc3c3fff000

def z692 : W := mkw 0x27ff6bd41f7f0000 0x04ffed7a83efe000 0xf7fffffe1fff8007 0xfeffffffc3fff000

def z693 : W := mkw 0x266f6a00077f0000 0x04cded4000efe000 0x107ffe0003ff8003 0x020fffc0007ff000

def z694 : W := mkw 0x0000c623043108c4 0x400018c460862118 0x8809ce678c7019e6 0xb10139ccf18e033c

def z695 : W := mkw 0x028540001c180000 0x0050a80003830000 0x4781c0000c000000 0x88f0380001800000

def z696 : W := mkw 0x0000000000000000 0x0000000000000000 0x1008001e00600781 0x02010003c00c00f0

def z697 : W := mkw 0x24c842001f7f0000 0x0499084003efe000 0xf7f800001fff8001 0xfeff000003fff000

def z698 : W := mkw 0x14d800941ac02500 0x029b0012835804a0 0xf7f8001e1fe00781 0xfeff0003c3fc00f0

def z699 : W := mkw 0x4fffe9f57c185856 0x09fffd3eaf830b0a 0xeff7c1e1fc1c787e 0xfdfef83c3f838f0f

def z700 : W := mkw 0x447afebfa4318ae5 0x488f5fd7f486315c 0x9879fe7f8c739fe7 0xb30f3fcff18e73fc

def z701 : W := mkw 0x111001d400807500 0x0222003a80100ea0 0x0000018000006000 0x0000003000000c00

def z702 : W := mkw 0x111011dca080f729 0x8222023b94101ee5 0x080001ffe0007ffc 0x0100003ffc000fff

def z703 : W := mkw 0x0b85d76bdc39daf7 0x4170baed7b873b5e 0xef87ffe1fc1ff87e 0xfdf0fffc3f83ff0f

def z704 : W := mkw 0x15d843d41ef17500 0x02bb087a83de2ea0 0xfff9fffe1ff3ff87 0xffff3fffc3fe7ff0

def z705 : W := mkw 0x0ba7e1615d1e5856 0x0174fc2c2ba3cb0a 0xfff7f1e1ff9ff87f 0xfffefe3c3ff3ff0f

def z706 : W := mkw 0x1fcdc1655e585956 0x03f9b82cabcb0b2a 0x4789c0660c601980 0x88f1380cc18c0330

def z707 : W := mkw 0x475d9dffe0000000 0x08ebb3bffc000000 0x47f9cfffe0000005 0xe8ff39fffc000000

def z708 : W := mkw 0x0b05c16144185856 0x0160b82c28830b0a 0x4f87c1e1e01c787e 0xe9f0f83c3c038f0f

def z709 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0xcfffffffe0100067 0xf9fffffffc02000c

def z710 : W := mkw 0x476fbd6fe0000000 0x08edf7adfc000000 0x478ffe7fe0000007 0xa8f1ffcffc000000

def z711 : W := mkw 0x308042001fff2500 0x0610084003ffe4a0 0xb00000001fff8780 0x1600000003fff0f0

def z712 : W := mkw 0x108042001ef17dc4 0x4210084003de2fb8 0xb80000001fe07f80 0x1700000003fc0ff0

def z713 : W := mkw 0x0b85c5635c185856 0x0170b8ac6b830b0a 0xef8fcfe7fc1c787e 0xfdf1f9fcff838f0f

def z714 : W := mkw 0x447a3e9ea1a7a6a9 0xc88f47d3d434f4d5 0x10783e1e03e38781 0x020f07c3c07c70f0

def z715 : W := mkw 0x474d8d674186a629 0x88e9b1ace830d4c5 0xff89ce66139fe678 0x9ff139ccc273fccf

def z716 : W := mkw 0x02a762001d3f0000 0x0054ec4003a7e000 0xf7fffe001fff8003 0xfeffffc003fff000

def z717 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x980fffffec739fe7 0xf301fffffd8e73fc

def z718 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xfffffe601fff9807 0xffffffcc03fff300

def z719 : W := mkw 0x2980c3615f7f5856 0x0530186c2befeb0a 0xb80001e1fffff87c 0x1700003c3fffff0f

def z720 : W := mkw 0x474d8d6740000000 0x08e9b1ace8000000 0xef8fcfe7f01c607e 0xfdf1f9fcfe038c0f

def z721 : W := mkw 0x477fbdffe186a629 0x88eff7bffc30d4c5 0x4fffffffe01fe67f 0xe9fffffffc03fccf

def z722 : W := mkw 0x109052989ef1ffe5 0x42120a5313de3ffc 0xb87031999ff3ffe7 0x770e063333fe7ffc

def z723 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xd7f9fe000ff38003 0xbaff3fc001fe7000

def z724 : W := mkw 0x24c842001f7f0000 0x0499084003efe000 0xb07800001fff8001 0x160f000003fff000

def z725 : W := mkw 0x2eef6a001f7f5856 0x05dded4003efeb0a 0xffffff81fffff87f 0xfffffff03fffff0f

def z726 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0xfff001fe1fe07f84 0x5ffe003fc3fc0ff0

def z727 : W := mkw 0x0b85c3615c395856 0x0170b86c2b872b0a 0xef87ffe1fc1ff87e 0xfdf0fffc3f83ff0f

def z728 : W := mkw 0x06ef28001b460000 0x00dde5000368c000 0xf7fffe001fff8003 0xfeffffc003fff000

def z729 : W := mkw 0x6190d7ffff7f0000 0x0c321affffefe000 0xb00001ffffff8004 0x1600003ffffff000

def z730 : W := mkw 0x43058d6340000000 0x0860b1ac68000000 0x4787cfe1e0000006 0xe8f0f9fc3c000000

def z731 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x1009fe7f8c639f87 0xa2013fcff18c73f0

def z732 : W := mkw 0x575d8df740807500 0x0aebb1bee8100ea0 0x4f89cffe00007f84 0x89f139ffc0000ff0

def z733 : W := mkw 0x0800d62b84398af7 0x41001ac57087315e 0x9809fe7f8c7f9fff 0xb3013fcff18ff3ff

def z734 : W := mkw 0x2fcdcf635e7958d6 0x45f9b9ec6bcf2b1a 0x4789ce660c601980 0x88f139ccc18c0330

def z735 : W := mkw 0x52a7bc2bfac07500 0x0a54f7857f580ea0 0xb807fe01ffe07f82 0x1700ffc03ffc0ff0

def z736 : W := mkw 0x0bb7f1f9fd9efe7f 0x8176fe3f3fb3dfcf 0x57f1f0780f839e01 0x8afe3e0f01f073c0

def z737 : W := mkw 0x066f3808a0000000 0x00cde70114000000 0x47fffe01e0000003 0xe8ffffc03c000000

def z738 : W := mkw 0x1b85c1655c185956 0x0370b82cab830b2a 0xef87c1e7fc1c79fe 0xfdf0f83cff838f3f

def z739 : W := mkw 0x2b85c3615e795856 0x0570b86c2bcf2b0a 0xef87c1e1fc7c787e 0xfdf0f83c3f8f8f0f

def z740 : W := mkw 0x0205000000000000 0x0040a00000000000 0xef87c181f01c607e 0xfdf0f8303e038c0f

def z741 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0xff87c1e1fc7c7ffe 0xfff0f83c3f8f8fff

def z742 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0xef8601e1fc1c787c 0x5df0c03c3f838f0f

def z743 : W := mkw 0x066f380880008221 0x00cde70110001044 0xdffffe1980138667 0xfbffffc3300270cc

def z744 : W := mkw 0x0000560a843182a1 0x40000ac150863054 0x9809fe7e0c739f87 0xb3013fcfc18e73f0

def z745 : W := mkw 0x0b85816158085012 0x0170b02c2b010a02 0xef87c1e1f01c607e 0xfdf0f83c3e038c0f

def z746 : W := mkw 0x047a309ca186a629 0x808f46139430d4c5 0x1078301e03838601 0x020f0603c07070c0

def z747 : W := mkw 0x247a3898a3c6a629 0x848f47131478d4c5 0x1070301803838601 0x020e0603007070c0

def z748 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0xb8763199ffffffff 0x770ec6333fffffff

def z749 : W := mkw 0x37ff29d43bce7508 0x86ffe53a8779cea1 0x67f60180738c6018 0x4cfec0300e718c03

def z750 : W := mkw 0x4227fe2be5378aed 0xc844ffc57ca6f15d 0x0007fe01e01f807a 0x0000ffc03c03f00f

def z751 : W := mkw 0x476f294440000000 0x08ede52888000000 0x47fffe0000000003 0xe8ffffc000000000

def z752 : W := mkw 0x577fbdffe0807500 0x0aeff7bffc100ea0 0x47ffffffe0006007 0xe8fffffffc000c00

def z753 : W := mkw 0x066f280001060000 0x00cde5000020c000 0x57fffe0003838003 0xeaffffc000707000

def z754 : W := mkw 0x0385816158005000 0x0070b02c2b000a00 0xef87c1e1fc1c787e 0xfdf0f83c3f838f0f

def z755 : W := mkw 0x1e5dc0b546d82d56 0x03cbb816a8db05aa 0x107fc01fe3fc07fb 0x020ff803fc7f80ff

def z756 : W := mkw 0x208052089f7f8221 0x04100a4113eff044 0xb80030199fff8667 0x3700060333fff0cc

def z757 : W := mkw 0x288042001d3f5856 0x0510084003a7eb0a 0xa80000001c1ff878 0x150000000383ff0f

def z758 : W := mkw 0x0448000000000000 0x0089000000000000 0x47f9fe0000000003 0xe8ff3fc000000000

def z759 : W := mkw 0x0305816140000000 0x0060b02c28000000 0x478fffe1e0000007 0xe8f1fffc3c000000

def z760 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x47fffe7fe0000003 0x88ffffcffc000000

def z761 : W := mkw 0x475d8df740000000 0x08ebb1bee8000000 0x4789cffe00000004 0x88f139ffc0000000

def z762 : W := mkw 0x477fbdffe0802400 0x08eff7bffc100480 0xffffffffffe07f87 0xfffffffffffc0ff0

def z763 : W := mkw 0x0980816158005856 0x0130102c2b000b0a 0xef8601e1fc1c787e 0xfdf0c03c3f838f0f

def z764 : W := mkw 0x33376bd405bf7500 0x0666ed7a80b7eea0 0x0807fffe001fff86 0x0100ffffc003fff0

def z765 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0x28763199f39fe67e 0x450ec6333e73fccf

def z766 : W := mkw 0x0205000000000000 0x0040a00000000000 0x478ffe0000000003 0xe8f1ffc000000000

def z767 : W := mkw 0x088042001c3958d6 0x4110084003872b1a 0xa80000001c7c79f8 0x15000000038f8f3f

def z768 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0xd7ffffffec600007 0xfafffffffd8c0000

def z769 : W := mkw 0x464d0c0600000000 0x08c9a180c0000000 0x4789ce0600000000 0x88f139c0c0000000

def z770 : W := mkw 0x066fbc2b81068221 0x00cdf7857020d044 0xfffffe7f939f8667 0xffffffcff273f0cc

def z771 : W := mkw 0x208042001e790000 0x0410084003cf2000 0xb00000001fe00000 0x1600000003fc0000

def z772 : W := mkw 0x475d9dffe0000000 0x08ebb3bffc000000 0x4789ffffe0000007 0xa8f13ffffc000000

def z773 : W := mkw 0x077fbdff80000000 0x00eff7bff0000000 0x47ffffff80000007 0xe8fffffff0000000

def z774 : W := mkw 0x208042001f7f5000 0x0410084003efea00 0xb80000001ffff800 0x1700000003ffff00

def z775 : W := mkw 0x208042001f7f0844 0x0410084003efe108 0xb80000001fff9860 0x1700000003fff30c

def z776 : W := mkw 0x0b85174ad829d2b3 0x4170a2e95b053a56 0x778e3f9e706fe799 0x4ef1c7f3ce0dfcf3

def z777 : W := mkw 0x14d800941ac02500 0x029b0012835804a0 0xfff8007e1fe01f85 0xffff000fc3fc03f0

def z778 : W := mkw 0x066f280001060000 0x00cde5000020c000 0x47fffe00001f8003 0xe8ffffc00003f000

def z779 : W := mkw 0x088042001c3958d6 0x4110084003872b1a 0x000000000c601980 0x00000000018c0330

def z780 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0xef8fc1fffc1c787f 0xfdf1f83fff838f0f

def z781 : W := mkw 0x066f280000000000 0x00cde50000000000 0xdffffe7e0c601f87 0xfbffffcfc18c03f0

def z782 : W := mkw 0x208042001f7f8221 0x0410084003eff044 0xb80000001fff8660 0x1700000003fff0cc

def z783 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x4fffffffe0001f87 0xe9fffffffc0003f0

def z784 : W := mkw 0x077fb9f9e0000000 0x00eff73f3c000000 0x47fffff9e0000007 0xe8ffffff3c000000

def z785 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0xfffe01fe7fec7f9d 0xffffc03fcffd8ff3

def z786 : W := mkw 0x0b8541405c185012 0x0170a8280b830a02 0xef87c181fc1c607e 0xfdf0f8303f838c0f

def z787 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0xf7fffffff3800007 0xfefffffffe700000

def z788 : W := mkw 0x308042001e795100 0x0610084003cf2a20 0x000000000c601980 0x00000000018c0330

def z789 : W := mkw 0x0b85c3615c395856 0x0170b86c2b872b0a 0xff8ffffffc7fffff 0xfff1ffffff8fffff

def z790 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0x30763199f39fe67b 0x460ec6333e73fccf

def z791 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xfffffe181fff8607 0xffffffc303fff0c0

def z792 : W := mkw 0x055895ff8080a621 0x00ab12bff01014c4 0xfff9ffff9393e667 0xffff3ffff2727ccc

def z793 : W := mkw 0x26efbc2b9b4e8ae5 0x44ddf7857369d15c 0x6ff6007f938c1fe4 0x4dfec00ff27183fc

def z794 : W := mkw 0x0b05816140005856 0x0160b02c28000b0a 0xef87c1e1f01c787e 0xfdf0f83c3e038f0f

def z795 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x47f7ffffe0000006 0x48fefffffc000000

def z796 : W := mkw 0x0980c1615c185856 0x0130182c2b830b0a 0x080001e1ec00787c 0x0100003c3d800f0f

def z797 : W := mkw 0x477f3ddee0000000 0x08efe7bbdc000000 0x47ffff9e60000003 0xe8fffff3cc000000

def z798 : W := mkw 0x0b05956bc000daf7 0x4160b2ad78001b5e 0x4f8fffffe0007fff 0xe9f1fffffc000fff

def z799 : W := mkw 0x0a8540001c185856 0x0150a80003830b0a 0xef87c181fc1c787e 0xfdf0f8303f838f0f

def z800 : W := mkw 0x43058d6340000000 0x0860b1ac68000000 0x4781ce6000000000 0x88f039cc00000000

def z801 : W := mkw 0x208042001f7f0000 0x0410084003efe000 0x000000000c7f8000 0x00000000018ff000

def z802 : W := mkw 0x0b05c16144180856 0x0160b82c2883010a 0xef87c1e1f01c607e 0xfdf0f83c3e038c0f

def z803 : W := mkw 0x066f28000186a629 0x80cde5000030d4c5 0xfffffe00139fe67b 0xffffffc00273fccf

def z804 : W := mkw 0x475d9dffe0000000 0x08ebb3bffc000000 0x4789ce7e00000000 0x88f139cfc0000000

def z805 : W := mkw 0x066f280001060000 0x00cde5000020c000 0x67fffe00138c0003 0xecffffc002718000

def z806 : W := mkw 0x467fbcbfa0000000 0x08cff797f4000000 0x47fffe7f80000007 0xe8ffffcff0000000

def z807 : W := mkw 0x1b85c1615e585956 0x0370b82c2bcb0b2a 0xef87c1e1fc7c79fe 0xfdf0f83c3f8f8f3f

def z808 : W := mkw 0x1032309ca186a729 0x820646139430d4e5 0xb876319ff39fe7ff 0x770ec633fe73fcff

def z809 : W := mkw 0x477fbdffe186a629 0x88eff7bffc30d4c5 0x77fffffff38fe61f 0xeefffffffe71fcc3

def z810 : W := mkw 0x057ab5ffa0000000 0x00af56bff4000000 0x47ffffffe0000007 0xe8fffffffc000000

def z811 : W := mkw 0x0305c16144100844 0x0060b82c28820108 0xef87c1e1fc1c787e 0xfdf0f83c3f838f0f

def z812 : W := mkw 0x431595ffe0000000 0x0862b2bffc000000 0x478fffffe0000007 0xe8f1fffffc000000

def z813 : W := mkw 0x2eef6a005f7f0012 0x05dded400befe002 0xf7fffe007fff801b 0xfeffffc00ffff003

def z814 : W := mkw 0x647a3e9ea3e7a629 0x8c8f47d3d47cf4c5 0x10783e1e03e38601 0x020f07c3c07c70c0

def z815 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xf7f9fe001fe38001 0xfeff3fc003fc7000

def z816 : W := mkw 0x475d9dffe0000000 0x08ebb3bffc000000 0x478fcfffe0000006 0xe8f1f9fffc000000

def z817 : W := mkw 0x4032349ea186a629 0x88064693d430d4c5 0xb876319ff39fe67f 0x770ec633fe73fccf

def z818 : W := mkw 0x2a27fe2bc53f8af7 0x4544ffc578a7f15e 0x0007fe01e01f807a 0x0000ffc03c03f00f

def z819 : W := mkw 0x2d6aab6143675856 0x05ad556c286ceb0a 0x18783fe1e3e3f87d 0x030f07fc3c7c7f0f

def z820 : W := mkw 0x066f280000000000 0x00cde50000000000 0x47f9fe0000000001 0x88ff3fc000000000

def z821 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x67fffffff00c601f 0xecfffffffe018c03

def z822 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x1009fe7f8c739fe3 0x82013fcff18e73fc

def z823 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0x57f801fe0fe01f85 0xeaff003fc1fc03f0

def z824 : W := mkw 0x0032e6b325b72ccc 0xc0065cd664b6e599 0x207fcfe67fec7998 0xc40ff9fccffd8f33

def z825 : W := mkw 0x208042001f7f08c4 0x4410084003efe118 0xb00000001fff9980 0x1600000003fff330

def z826 : W := mkw 0x466fac2340000000 0x08cdf58468000000 0x47fffe0000000003 0xe8ffffc000000000

def z827 : W := mkw 0x15d8d7ff9ef1ffe5 0x42bb1afff3de3ffc 0x67f1ff819393e062 0x4cfe3ff032727c0c

def z828 : W := mkw 0x066f3c0a80000000 0x00cde78150000000 0x47fffe1e00000003 0xe8ffffc3c0000000

def z829 : W := mkw 0x155895ff8080ffe5 0x42ab12bff0101ffc 0x4ff9ffff80007fe7 0xe9ff3ffff0000ffc

def z830 : W := mkw 0x17ff29d41bc67500 0x02ffe53a8378cea0 0xfffffffe1fffff87 0xffffffffc3fffff0

def z831 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xfffffe019fff8067 0xffffffc033fff00c

def z832 : W := mkw 0x208042001f7f82a1 0x4410084003eff054 0xb00000001fff8780 0x1600000003fff0f0

def z833 : W := mkw 0x076fa96141060000 0x00edf52c2820c000 0xffffffe1f39fe07f 0xfffffffc3e73fc0f

def z834 : W := mkw 0x001010988080a621 0x00020213101014c4 0xb8763199f39fe67f 0x770ec6333e73fccf

def z835 : W := mkw 0x188042001ef9fff7 0x4310084003df3ffe 0xb80000001ffffff8 0x1700000003ffffff

def z836 : W := mkw 0x24ea6a001f770000 0x049d4d4003eee000 0xf7f9fe001ff38003 0xfeff3fc003fe7000

def z837 : W := mkw 0x476fad6741060000 0x08edf5ace820c000 0xf7fffe66139f8003 0xfeffffccc273f000

def z838 : W := mkw 0x477f6bd464318ae5 0x48efed7a8c86315c 0xdff601806c739fe0 0x5bfec0300d8e73fc

def z839 : W := mkw 0x0448000000000000 0x0089000000000000 0xf7f8000013800001 0xfeff000002700000

def z840 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xf7f7fe001fff8002 0x5efeffc003fff000

def z841 : W := mkw 0x066f280000000000 0x00cde50000000000 0x47ffff81e0000007 0xe8fffff03c000000

def z842 : W := mkw 0x476fbd6fe0000000 0x08edf7adfc000000 0x478fffe7e0000006 0xe8f1fffcfc000000

def z843 : W := mkw 0x15ea314cbb46d329 0x82bd46299768da65 0x478e3067ec7f99fa 0x88f1c60cfd8ff33f

def z844 : W := mkw 0x466fbc2be1068229 0x88cdf7857c20d045 0xf7fffe01f39f807b 0xfeffffc03e73f00f

def z845 : W := mkw 0x577fbdffe0807500 0x0aeff7bffc100ea0 0xdfffffffec607f87 0xfbfffffffd8c0ff0

def z846 : W := mkw 0x474d9d6fe0000000 0x08e9b3adfc000000 0x4789ce67e0000000 0x88f139ccfc000000

def z847 : W := mkw 0x4f7fbdffe0005856 0x09eff7bffc000b0a 0x47ffffffe0001807 0xe8fffffffc000300

def z848 : W := mkw 0x0032209001862400 0x000644120030c480 0xb8763199f39fe67f 0x770ec6333e73fccf

def z849 : W := mkw 0x455895ffe0000000 0x08ab12bffc000000 0x47f9ffffe0000007 0xe8ff3ffffc000000

def z850 : W := mkw 0x0b8541405c185856 0x0170a8280b830b0a 0xef860181fc1c787e 0x7df0c0303f838f0f

def z851 : W := mkw 0x477f29d460000000 0x08efe53a8c000000 0x47f7ff8060000002 0x48fefff00c000000

def z852 : W := mkw 0x477fbdffe1068229 0x88eff7bffc20d045 0xdfffffffe01f867f 0xfbfffffffc03f0cf

def z853 : W := mkw 0x477fbdffe1060000 0x08eff7bffc20c000 0x67fffffff38c0007 0xecfffffffe718000

def z854 : W := mkw 0x05c801401a405000 0x00b9002803480a00 0xfff801fe1fe07f85 0xffff003fc3fc0ff0

def z855 : W := mkw 0x476fad6740000000 0x08edf5ace8000000 0x47ffffe7e0000007 0xe8fffffcfc000000

def z856 : W := mkw 0x308042001ffff729 0x8610084003fffee5 0xb80000001ffffff8 0x1700000003ffffff

def z857 : W := mkw 0x575d8df742c02500 0x0aebb1bee85804a0 0x57f9ce7e03e00781 0x8aff39cfc07c00f0

def z858 : W := mkw 0x36ef6a041f7f0100 0x06dded4083efe020 0xf7fffe061fff8183 0xfeffffc0c3fff030

def z859 : W := mkw 0x4f7fbdffe0080012 0x09eff7bffc010002 0x47ffffffe00c001f 0xe8fffffffc018003

def z860 : W := mkw 0x046a280001060000 0x008d45000020c000 0x10783e0003838001 0x020f07c000707000

def z861 : W := mkw 0x098041401c185856 0x0130082803830b0a 0xef8601e1fc1c787e 0xfdf0c03c3f838f0f

def z862 : W := mkw 0x475d9dffc0000000 0x08ebb3bff8000000 0x47f9ffff80000007 0xe8ff3ffff0000000

def z863 : W := mkw 0x074d094400000000 0x00e9a12880000000 0x4789ce6600000000 0x88f139ccc0000000

def z864 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0xb8760199f39fe67c 0x570ec0333e73fccf

def z865 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0x77f801fe1fe07f81 0xceff003fc3fc0ff0

def z866 : W := mkw 0x0b85816158085856 0x0170b02c2b010b0a 0xef8601e1fc0c787c 0xfdf0c03c3f818f0f

def z867 : W := mkw 0x577fbdffe0807500 0x0aeff7bffc100ea0 0xfffffffff3807f87 0xfffffffffe700ff0

def z868 : W := mkw 0x577fbdffe2c02500 0x0aeff7bffc5804a0 0xfffffffff3e06787 0xfffffffffe7c0cf0

def z869 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x47f9fffe00000005 0xe8ff3fffc0000000

def z870 : W := mkw 0x22a76a001f7f0000 0x0454ed4003efe000 0xb00600001fff8000 0x1600c00003fff000

def z871 : W := mkw 0x05d801d41a400000 0x00bb003a83480000 0xfff801fe1fe01f85 0xffff003fc3fc03f0

def z872 : W := mkw 0x447a389ca186a629 0x888f47139430d4c5 0x1070301803838601 0x020e0603007070c0

def z873 : W := mkw 0x477fbdffe186a629 0x88eff7bffc30d4c5 0x67fffffff39fe07f 0xecfffffffe73fc0f

def z874 : W := mkw 0x40323c9aa186a629 0x880647935430d4c5 0xb8763f99f39fe67f 0x770ec7f33e73fccf

def z875 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x47ffffe7e0000002 0xc8fffffcfc000000

def z876 : W := mkw 0x4f7fbdffe0000856 0x09eff7bffc00010a 0x47ffffffe000007f 0xe8fffffffc00000f

def z877 : W := mkw 0x0285c0211c180844 0x0050b80423830108 0xef87c1e1fc1c787e 0xfdf0f83c3f838f0f

def z878 : W := mkw 0x477fbdffe080a621 0x08eff7bffc1014c4 0xfffffffff393e667 0xfffffffffe727ccc

def z879 : W := mkw 0x4cfa7c9ebc185856 0x099f4f93d7830b0a 0xa8783e1e1c1c7879 0x150f07c3c3838f0f

def z880 : W := mkw 0x06ef6a001e710000 0x00dded4003ce2000 0xf7fffe001ff38003 0xfeffffc003fe7000

def z881 : W := mkw 0x208042001f7f0000 0x0410084003efe000 0xb07000001fff8001 0x760e000003fff000

def z882 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xf7fffe661fff9983 0xfeffffccc3fff330

def z883 : W := mkw 0x577fbdffe080ffe5 0x4aeff7bffc101ffc 0x4fffffffe0007fe7 0xe9fffffffc000ffc

def z884 : W := mkw 0x10b27298bff7ffed 0xc2164e5317fefffd 0xb8763199ffffffff 0x770ec6333fffffff

def z885 : W := mkw 0x20a262001f7f0000 0x04144c4003efe000 0xb07030001fff8001 0x160e060003fff000

def z886 : W := mkw 0x0800d62bc4318af7 0x41001ac57886315e 0x9809fe7fec739fff 0xb3013fcffd8e73ff

def z887 : W := mkw 0x474d9d6fc0000000 0x08e9b3adf8000000 0x4789fe6780000002 0x88f13fccf0000000

def z888 : W := mkw 0x0000520884318221 0x00000a4110863044 0x9809fe7f8c739fe7 0xb3013fcff18e73fc

def z889 : W := mkw 0x4f7fbdffe0005012 0x09eff7bffc000a02 0x47ffffffe000601f 0xe8fffffffc000c03

def z890 : W := mkw 0x26ef28001b4e0000 0x04dde5000369c000 0xf7fffe00139f8003 0xfeffffc00273f000

def z891 : W := mkw 0x067f3898a080a629 0x80cfe713141014c5 0x4fffff99e000667f 0xe9fffff33c000ccf

def z892 : W := mkw 0x466f3c0aa0000000 0x08cde78154000000 0x47fffe0000000003 0xe8ffffc000000000

def z893 : W := mkw 0x20b27298bfffa629 0x84164e5317fff4c5 0xb07030181fff8601 0x160e060303fff0c0

def z894 : W := mkw 0x0fefe9615d1e5856 0x01fdfd2c2ba3cb0a 0xffffffe1ff9ff87f 0xfffffffc3ff3ff0f

def z895 : W := mkw 0x4f7fbdffe186fe7f 0x89eff7bffc30dfcf 0xfffffffff39ffe7f 0xfffffffffe73ffcf

def z896 : W := mkw 0x34d842941fff2500 0x069b085283ffe4a0 0xb078001e1fff8781 0x160f0003c3fff0f0

def z897 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0x5ff801fe0fe07f85 0x8bff003fc1fc0ff0

def z898 : W := mkw 0x476fbd6fe0000000 0x08edf7adfc000000 0x4789fe6600000000 0x88f13fccc0000000

def z899 : W := mkw 0x477fbdffe186a629 0x88eff7bffc30d4c5 0xf7fffffff39f8607 0xfefffffffe73f0c0

def z900 : W := mkw 0x4b85cd635c185856 0x0970b9ac6b830b0a 0xef87cfe1fc1c787e 0xfdf0f9fc3f838f0f

def z901 : W := mkw 0x477fbdffe0008ae5 0x48eff7bffc00115c 0xdfffffffec601fe7 0xfbfffffffd8c03fc

def z902 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x47ffffffec601987 0xe8fffffffd8c0330

def z903 : W := mkw 0x208042001fff2408 0x8410084003ffe481 0xb00000001fffe018 0x1600000003fffc03

def z904 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x47f9fe7f80000007 0xa8ff3fcff0000000

def z905 : W := mkw 0x15d801d43ac07508 0x82bb003a87580ea1 0xfff801fe7fe07f9d 0xffff003fcffc0ff3

def z906 : W := mkw 0x076fbd6bc0000000 0x00edf7ad78000000 0x47ffffffe0000007 0xe8fffffffc000000

def z907 : W := mkw 0x474d8d6740000000 0x08e9b1ace8000000 0x478fcfe660000000 0xc8f1f9fccc000000

def z908 : W := mkw 0x477fbdffe0008ae5 0x48eff7bffc00115c 0x47ffffffe0000067 0xe8fffffffc00000c

def z909 : W := mkw 0x4f7fbdffe0005856 0x09eff7bffc000b0a 0xeffffffff01c787f 0xfdfffffffe038f0f

def z910 : W := mkw 0x0000d62b84310000 0x00001ac570862000 0x9809fe7f8c739f87 0xb3013fcff18e73f0

def z911 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xf7ffff807fffe01b 0xfefffff00ffffc03

def z912 : W := mkw 0x04c8942b9a408ae5 0x409912857348115c 0xfff8007f9fe01fe5 0xffff000ff3fc03fc

def z913 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0xe7fffffff01c0007 0xfcfffffffe038000

def z914 : W := mkw 0x208042001f7f0000 0x0410084003efe000 0x100000000fe38000 0x0200000001fc7000

def z915 : W := mkw 0x0000d62ba4318aed 0xc0001ac57486315d 0x9809fe7fec739fff 0xb3013fcffd8e73ff

def z916 : W := mkw 0x24ea6a001f7f0000 0x049d4d4003efe000 0xb07000001fff8000 0x160e000003fff000

def z917 : W := mkw 0x476fad6740000000 0x08edf5ace8000000 0x47f9fe6600000001 0x88ff3fccc0000000

def z918 : W := mkw 0x111095ffa080ffed 0xc22212bff4101ffd 0x080001ffe0007ffc 0x0100003ffc000fff

def z919 : W := mkw 0x475d8df740000000 0x08ebb1bee8000000 0x47ffcfffe0000007 0xe8fff9fffc000000

def z920 : W := mkw 0x57ff29d47bc67508 0x8affe53a8f78cea1 0x67f60180738c6018 0x4cfec0300e718c03

def z921 : W := mkw 0x074d896140000000 0x00e9b12c28000000 0x4789ce6000000000 0x88f139cc00000000

def z922 : W := mkw 0x08b27298bdbffeff 0xc1164e5317b7ffdf 0xb8763199ffffffff 0x770ec6333fffffff

def z923 : W := mkw 0x4f7fbdffe080fe7f 0x89eff7bffc101fcf 0x4fffffffe0007e7f 0xe9fffffffc000fcf

def z924 : W := mkw 0x064d9c2b80000000 0x00c9b38570000000 0x4789fe7f80000007 0xa8f13fcff0000000

def z925 : W := mkw 0x208042001f7f0000 0x0410084003efe000 0x200000001fec0000 0x0400000003fd8000

def z926 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x47f7ff99e0000007 0x68fefff33c000000

def z927 : W := mkw 0x20a262001f7f0000 0x04144c4003efe000 0xb00630001fff8002 0x1600c60003fff000

def z928 : W := mkw 0x577fbdffe3c6a729 0x8aeff7bffc78d4e5 0x57ffffffe3e38787 0xeafffffffc7c70f0

def z929 : W := mkw 0x0b85816158085856 0x0170b02c2b010b0a 0x6f87c1e1f00c787e 0xedf0f83c3e018f0f

def z930 : W := mkw 0x477fadf760000000 0x08eff5beec000000 0x47ffcffe60000005 0xe8fff9ffcc000000

def z931 : W := mkw 0x066f280002400000 0x00cde50000480000 0x57fffe0003e00003 0xeaffffc0007c0000

def z932 : W := mkw 0x075d95ffc0000000 0x00ebb2bff8000000 0x47ffffffe0000007 0xe8fffffffc000000

def z933 : W := mkw 0x474d8d6740000000 0x08e9b1ace8000000 0x4789ce7e00000005 0xa8f139cfc0000000

def z934 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0xe787c181fc1c607a 0xfcf0f8303f838c0f

def z935 : W := mkw 0x20a27208bf7f8229 0x84144e4117eff045 0xb0063001ffff807a 0x1600c6003ffff00f

def z936 : W := mkw 0x36ef6a001f7f5100 0x06dded4003efea20 0xf7fffe001fff9983 0xfeffffc003fff330

def z937 : W := mkw 0x26ef6a001f7f5000 0x04dded4003efea00 0xfffffe001ffff803 0xffffffc003ffff00

def z938 : W := mkw 0x26ef6a001f7f0844 0x04dded4003efe108 0xfffffe001fff9863 0xffffffc003fff30c

def z939 : W := mkw 0x0385c1615c180000 0x0070b82c2b830000 0xef87c1e1fc1c607e 0xfdf0f83c3f838c0f

def z940 : W := mkw 0x266f6a00077f0000 0x04cded4000efe000 0x57fffe0003ff8003 0xeaffffc0007ff000

def z941 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xf7fffe7e1fff8007 0xfeffffcfc3fff000

def z942 : W := mkw 0x474d8d6740000000 0x08e9b1ace8000000 0xdf89ce7e0c601f85 0xbbf139cfc18c03f0

def z943 : W := mkw 0x26dd5a98bef9a629 0x84dbab5317df34c5 0x4f89cf99ec60667c 0x89f139f33d8c0ccf

def z944 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0xb87e31fff39fe67f 0xf70fc63ffe73fccf

def z945 : W := mkw 0x4b85c5675c185856 0x0970b8aceb830b0a 0xef87c1e7fc1c787e 0xfdf0f83cff838f0f

def z946 : W := mkw 0x677fbdffe10e0000 0x0ceff7bffc21c000 0x47ffffffe00c0007 0xe8fffffffc018000

def z947 : W := mkw 0x20b27298bfffaeed 0xc4164e5317fff5dd 0xb8763199ffffffff 0x770ec6333fffffff

def z948 : W := mkw 0x467f289420000000 0x08cfe51284000000 0x47fffe0000000003 0xe8ffffc000000000

def z949 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x9809fe7e0c639f85 0xb3013fcfc18c73f0

def z950 : W := mkw 0x5f7fbdffe0807d56 0x0beff7bffc100faa 0x4fffffffe0007fff 0xe9fffffffc000fff

def z951 : W := mkw 0x476fad6740000000 0x08edf5ace8000000 0x47ffce6600000000 0xc8fff9ccc0000000

def z952 : W := mkw 0x474d8d6740000000 0x08e9b1ace8000000 0x478fce67e0000002 0x88f1f9ccfc000000

def z953 : W := mkw 0x577fbdffe0802500 0x0aeff7bffc1004a0 0x47ffffffe0000787 0xe8fffffffc0000f0

def z954 : W := mkw 0x108042001ef17500 0x0210084003de2ea0 0xb80000001ff3ff80 0x1700000003fe7ff0

def z955 : W := mkw 0x476fbd6fe0000000 0x08edf7adfc000000 0x4787fe01e0000002 0x08f0ffc03c000000

def z956 : W := mkw 0x066fbc2b80000000 0x00cdf78570000000 0x47fffe0180000003 0xe8ffffc030000000

def z957 : W := mkw 0x477fbdffe0008221 0x08eff7bffc001044 0x57ffffffe0038607 0xeafffffffc0070c0

def z958 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xf7fffe1e1fff8783 0xfeffffc3c3fff0f0

def z959 : W := mkw 0x067f289400000000 0x00cfe51280000000 0x47fffe1e00000003 0xe8ffffc3c0000000

def z960 : W := mkw 0x477fbdffe186a629 0x88eff7bffc30d4c5 0xffffffffffffffff 0xffffffffffffffff

def z961 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0x6f87c1e1f01c787e 0x4df0f83c3e038f0f

def z962 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0xfff7c1e1ff9c787f 0xfffef83c3ff38f0f

def z963 : W := mkw 0x477fbdffe080a629 0x88eff7bffc1014c5 0xfffffffff380667f 0xfffffffffe700ccf

def z964 : W := mkw 0x476fad6760000000 0x08edf5acec000000 0x478fce6660000000 0x88f1f9cccc000000

def z965 : W := mkw 0x008042001c390000 0x0010084003872000 0xb00000001c7f8000 0x16000000038ff000

def z966 : W := mkw 0x4327bd6be0000000 0x0864f7ad7c000000 0x4787ff81e0000002 0x48f0fff03c000000

def z967 : W := mkw 0x467fbcbbe0000000 0x08cff7977c000000 0x47ffff99e0000007 0xe8fffff33c000000

def z968 : W := mkw 0x0080000018000000 0x0010000003000000 0xef860181fc1c607e 0xfdf0c0303f838c0f

def z969 : W := mkw 0x0b85c1615e585856 0x0170b82c2bcb0b0a 0xff87c1e1fffc787e 0xfff0f83c3fff8f0f

def z970 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0xff8fc1e1fc7c787f 0xfff1f83c3f8f8f0f

def z971 : W := mkw 0x066f280000000000 0x00cde50000000000 0xe7fffe00101c0003 0xfcffffc002038000

def z972 : W := mkw 0x00323098a1060000 0x000646131420c000 0xb8763199f39fe07f 0x770ec6333e73fc0f

def z973 : W := mkw 0x26ef6a001f7f08c4 0x44dded4003efe118 0xf7fffe001fff9983 0xfeffffc003fff330

def z974 : W := mkw 0x1fcdc7675e7959d6 0x43f9b8ecebcf2b3a 0x4789ce660c601980 0x88f139ccc18c0330

def z975 : W := mkw 0x477fbdffe186a629 0x88eff7bffc30d4c5 0xfff7ff99f39fe67f 0x7ffefff33e73fccf

def z976 : W := mkw 0x06ef68001d1e0000 0x00dded0003a3c000 0xf7fffe001f9f8003 0xfeffffc003f3f000

def z977 : W := mkw 0x477fadf740000000 0x08eff5bee8000000 0x47fffffe00000007 0xe8ffffffc0000000

def z978 : W := mkw 0x28a262001f7f5856 0x05144c4003efeb0a 0xb8763181fffff87f 0x770ec6303fffff0f

def z979 : W := mkw 0x067f289020000000 0x00cfe51204000000 0x47ffff8060000003 0xe8fffff00c000000

def z980 : W := mkw 0x066f280001060000 0x00cde5000020c000 0x67f60000138c0000 0x4cfec00002718000

def z981 : W := mkw 0x411095ffe080aeed 0xc82212bffc1015dd 0x080001ffe0007ffc 0x0100003ffc000fff

def z982 : W := mkw 0x475d8df740000000 0x08ebb1bee8000000 0x47f9ce7e00000001 0x88ff39cfc0000000

def z983 : W := mkw 0x008042001e718ae5 0x4010084003ce315c 0xb80000001ff39fe0 0x1700000003fe73fc

def z984 : W := mkw 0x0305956bc0008221 0x0060b2ad78001044 0xff8ffffff01fe67f 0xfff1fffffe03fccf

def z985 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0xb87631fff39fffff 0x770ec63ffe73ffff

def z986 : W := mkw 0x3fcdcb655e795956 0x07f9b96cabcf2b2a 0x4789ce660c601980 0x88f139ccc18c0330

def z987 : W := mkw 0x208042001f7f0000 0x0410084003efe000 0xb80000001fffe078 0x1700000003fffc0f

def z988 : W := mkw 0x477fbdffe186a629 0x88eff7bffc30d4c5 0xfffffffff383e607 0xfffffffffe707cc0

def z989 : W := mkw 0x319043d41fff7500 0x0632087a83ffeea0 0xb80001fe1fffff84 0x1700003fc3fffff0

def z990 : W := mkw 0x155801d402c02500 0x02ab003a805804a0 0xdff801fe0fe01f85 0xfbff003fc1fc03f0

def z991 : W := mkw 0x008042001e710000 0x0010084003ce2000 0xb00000001ff38000 0x1600000003fe7000

def z992 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0x4f87c1e1ec1c787e 0x89f0f83c3d838f0f

def z993 : W := mkw 0x477fbdffe1068229 0x88eff7bffc20d045 0xf7fffffff39f807f 0xfefffffffe73f00f

def z994 : W := mkw 0x247a3e9aa3e7a6a9 0xc48f47d3547cf4d5 0x10783e1e03e38781 0x020f07c3c07c70f0

def z995 : W := mkw 0x477f39dce0000000 0x08efe73b9c000000 0x47ffff99e0000007 0xe8fffff33c000000

def z996 : W := mkw 0x0305856340000000 0x0060b0ac68000000 0x4789ce6600000000 0x88f139ccc0000000

def z997 : W := mkw 0x064d8c2300000000 0x00c9b18460000000 0x4789ce6600000000 0x88f139ccc0000000

def z998 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0x77fffe0013ff8003 0x4effffc0027ff000

def z999 : W := mkw 0x0980d76bdc39daf7 0x41301aed7b873b5e 0xb80001fffc7ffffc 0x1700003fff8fffff

def z1000 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x47ffff81e0000003 0xe8fffff03c000000

def z1001 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0xeffffffff0006007 0xfdfffffffe000c00

def z1002 : W := mkw 0x0305956bc0000000 0x0060b2ad78000000 0x4787ffe1e0000006 0xe8f0fffc3c000000

def z1003 : W := mkw 0x511095ffe080ffe5 0x4a2212bffc101ffc 0x080001ffe0007fe4 0x0100003ffc000ffc

def z1004 : W := mkw 0x208042001f7f0000 0x0410084003efe000 0xb80000001fff9f80 0x1700000003fff3f0

def z1005 : W := mkw 0x208042001f7f8ae5 0x4410084003eff15c 0xb00000001fff8060 0x1600000003fff00c

def z1006 : W := mkw 0x577fbdffe0005100 0x0aeff7bffc000a20 0x47ffffffe0001987 0xe8fffffffc000330

def z1007 : W := mkw 0x476fad6740000000 0x08edf5ace8000000 0x478ffe6600000002 0x88f1ffccc0000000

def z1008 : W := mkw 0x26cd4a001e790000 0x04d9a94003cf2000 0xf7f9fe001ff38003 0xfeff3fc003fe7000

def z1009 : W := mkw 0x0305956bc0000000 0x0060b2ad78000000 0x4789fe7f80000007 0xa8f13fcff0000000

def z1010 : W := mkw 0x177f29d400807500 0x02efe53a80100ea0 0x4ffffffe00007f87 0xe9ffffffc0000ff0

def z1011 : W := mkw 0x208042001f7f0000 0x0410084003efe000 0xb00600001fff8002 0x7600c00003fff000

def z1012 : W := mkw 0x477fbdffe080a629 0x88eff7bffc1014c5 0x47ffffffe0000607 0xe8fffffffc0000c0

def z1013 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0xb809ffff9c73ffe7 0xf7013ffff38e7ffc

def z1014 : W := mkw 0x477fbdffe186a629 0x88eff7bffc30d4c5 0x6ffffffff38c667f 0xedfffffffe718ccf

def z1015 : W := mkw 0x4327bd6be1068229 0x8864f7ad7c20d045 0xef87ffe1f01fe07e 0xfdf0fffc3e03fc0f

def z1016 : W := mkw 0x066f280000000000 0x00cde50000000000 0xd7fffe0000138003 0xfaffffc000027000

def z1017 : W := mkw 0x0305856340000000 0x0060b0ac68000000 0x478fcfe7e0000006 0xe8f1f9fcfc000000

def z1018 : W := mkw 0x0b85c3615c3958d6 0x4170b86c2b872b1a 0xef87c1e1fc7c79fe 0xfdf0f83c3f8f8f3f

def z1019 : W := mkw 0x066fbc2b80008ae5 0x40cdf7857000115c 0x4ffffe7f80001fe7 0xe9ffffcff00003fc

def z1020 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0xef8fc1e7fc7c79fe 0xfdf1f83cff8f8f3f

def z1021 : W := mkw 0x0100956b80000000 0x002012ad70000000 0x4789ffff80000007 0xe8f13ffff0000000

def z1022 : W := mkw 0x477fbdffe0008221 0x08eff7bffc001044 0xfffffffff01fe67f 0xfffffffffe03fccf

def z1023 : W := mkw 0x467fbcbbe186a629 0x88cff7977c30d4c5 0xffffff99f39fe67f 0xfffffff33e73fccf

def z1024 : W := mkw 0x2080d62b9f7f8ae5 0x44101ac573eff15c 0xb800007f9fff9fe4 0x1700000ff3fff3fc

def z1025 : W := mkw 0x4f7fbdffe000daf7 0x49eff7bffc001b5e 0x4fffffffe0007fff 0xe9fffffffc000fff

def z1026 : W := mkw 0x088042001c39daf7 0x4110084003873b5e 0x980000000c739fe0 0x13000000018e73fc

def z1027 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0x67fffe001fff8002 0xccffffc003fff000

def z1028 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x9809fe7e0c739fe1 0x93013fcfc18e73fc

def z1029 : W := mkw 0x466fbc2be0000000 0x08cdf7857c000000 0x47fffe7fe0000007 0xe8ffffcffc000000

def z1030 : W := mkw 0x0227280000000000 0x0044e50000000000 0x4787fe0000000002 0xe8f0ffc000000000

def z1031 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x57ffffffe0600787 0xeafffffffc0c00f0

def z1032 : W := mkw 0x491095ffe080fe7f 0x892212bffc101fcf 0x080001ffe0007e7c 0x0100003ffc000fcf

def z1033 : W := mkw 0x0f6fa96140005856 0x01edf52c28000b0a 0x4fffffe1e000787f 0xe9fffffc3c000f0f

def z1034 : W := mkw 0x477fbdffe0802400 0x08eff7bffc100480 0x57ffffffe3800607 0xeafffffffc7000c0

def z1035 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x9809ffffec73ffff 0xb3013ffffd8e7fff

def z1036 : W := mkw 0x0b85014058085012 0x0170a0280b010a02 0x67860181f01c607a 0x4cf0c0303e038c0f

def z1037 : W := mkw 0x475d9dffe080a629 0x88ebb3bffc1014c5 0x4f89cfffe000667c 0x89f139fffc000ccf

def z1038 : W := mkw 0x066f280000000000 0x00cde50000000000 0xf7fffe0013800003 0xfeffffc002700000

def z1039 : W := mkw 0x077fa9f540000000 0x00eff53ea8000000 0x47ffffffe0000007 0xe8fffffffc000000

def z1040 : W := mkw 0x191095ffc080fff7 0x432212bff8101ffe 0x080001ffe0007ffc 0x0100003ffc000fff

def z1041 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xfffffe001fffe07b 0xffffffc003fffc0f

def z1042 : W := mkw 0x066f280000000000 0x00cde50000000000 0x47fffe7e00000007 0xe8ffffcfc0000000

def z1043 : W := mkw 0x477f39dce186a629 0x88efe73b9c30d4c5 0xffffff99f39fe67f 0xfffffff33e73fccf

def z1044 : W := mkw 0x477f3ddea0000000 0x08efe7bbd4000000 0x47fffffe00000007 0xe8ffffffc0000000

def z1045 : W := mkw 0x288042001e795856 0x0510084003cf2b0a 0x000000000c601800 0x00000000018c0300

def z1046 : W := mkw 0x077f29d400000000 0x00efe53a80000000 0x47ffff8000000003 0xe8fffff000000000

def z1047 : W := mkw 0x111043d404b17500 0x0222087a80962ea0 0x9809fffe0c73ff87 0xb3013fffc18e7ff0

def z1048 : W := mkw 0x076f294400000000 0x00ede52880000000 0x47fffe6600000003 0xe8ffffccc0000000

def z1049 : W := mkw 0x477fbdffe1060000 0x08eff7bffc20c000 0xfffffffff39fe07f 0xfffffffffe73fc0f

def z1050 : W := mkw 0x477fbdffe1068221 0x08eff7bffc20d044 0xfffffffff39f8667 0xfffffffffe73f0cc

def z1051 : W := mkw 0x476fbd6fe0000000 0x08edf7adfc000000 0x47fffe67e0000003 0xe8ffffccfc000000

def z1052 : W := mkw 0x474d8d6740000000 0x08e9b1ace8000000 0x4789cfe600000004 0xe8f139fcc0000000

def z1053 : W := mkw 0x066f280000000000 0x00cde50000000000 0xd7fffe000c600003 0xfaffffc0018c0000

def z1054 : W := mkw 0x06cd42001e790000 0x00d9a84003cf2000 0xf7fffe001fff8003 0xfeffffc003fff000

def z1055 : W := mkw 0x577fbdffe186f729 0x8aeff7bffc30dee5 0xfffffffff39fffff 0xfffffffffe73ffff

def z1056 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0x57fffe000fe38003 0xeaffffc001fc7000

def z1057 : W := mkw 0x577fbdffe3c6a729 0x8aeff7bffc78d4e5 0xfffffffff3ffe7ff 0xfffffffffe7ffcff

def z1058 : W := mkw 0x003220902186a629 0x800644120430d4c5 0xb8760181f39fe67e 0x770ec0303e73fccf

def z1059 : W := mkw 0x477fbdffe1862408 0x88eff7bffc30c481 0xf7fffffff39fe01f 0xfefffffffe73fc03

def z1060 : W := mkw 0x0b85816158085856 0x0170b02c2b010b0a 0x67860181f00c6078 0x4cf0c0303e018c0f

def z1061 : W := mkw 0x0000c623043108c4 0x400018c460862118 0x9809fe7e0c739f87 0xb3013fcfc18e73f0

def z1062 : W := mkw 0x266f6a0007770000 0x04cded4000eee000 0xd7fffe000ff38003 0xfaffffc001fe7000

def z1063 : W := mkw 0x077f29d401862400 0x00efe53a8030c480 0xfffffffe139fe607 0xffffffffc273fcc0

def z1064 : W := mkw 0x04d800901ac02400 0x009b001203580480 0xfff801fe1fe07f85 0xffff003fc3fc0ff0

def z1065 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x1809fe7f8c639fe5 0x83013fcff18c73fc

def z1066 : W := mkw 0x066f280000000000 0x00cde50000000000 0x478ffe0000000002 0x88f1ffc000000000

def z1067 : W := mkw 0x066f280000000000 0x00cde50000000000 0x47f7fe0000000002 0x48feffc000000000

def z1068 : W := mkw 0x108042001e7159c4 0x4210084003ce2b38 0x000000000c601980 0x00000000018c0330

def z1069 : W := mkw 0x20a272089f7f8ae5 0x44144e4113eff15c 0xb87630199fff9fe7 0x770ec60333fff3fc

def z1070 : W := mkw 0x477fbdffe080a629 0x88eff7bffc1014c5 0xeffffffff01c667f 0xfdfffffffe038ccf

def z1071 : W := mkw 0x466f2c0600000000 0x08cde580c0000000 0x47fffe0600000003 0xe8ffffc0c0000000

def z1072 : W := mkw 0x167f289402c02500 0x02cfe512805804a0 0x57fffe1e03e00783 0xeaffffc3c07c00f0

def z1073 : W := mkw 0x088042001c395856 0x0110084003872b0a 0xb80000001c7ff878 0x17000000038fff0f

def z1074 : W := mkw 0x266f2a0003670000 0x04cde540006ce000 0x57f9fe0003e38001 0x8aff3fc0007c7000

def z1075 : W := mkw 0x0032349aa186a629 0x800646935430d4c5 0xb87e3f9ff39fe67f 0x770fc7f3fe73fccf

def z1076 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0x20763199f39fe07f 0x640ec6333e73fc0f

def z1077 : W := mkw 0x147a309ca3c6a729 0x828f46139478d4e5 0x1070301803838601 0x020e0603007070c0

def z1078 : W := mkw 0x477fadf760000000 0x08eff5beec000000 0x47ffcfe7e0000006 0xe8fff9fcfc000000

def z1079 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0xb809fe7f9c7fffff 0xb7013fcff38fffff

def z1080 : W := mkw 0x077f39dca186a629 0x80efe73b9430d4c5 0xfffffffff39fe67f 0xfffffffffe73fccf

def z1081 : W := mkw 0x15c801441a405100 0x02b9002883480a20 0xfff8007e1fe01f85 0xffff000fc3fc03f0

def z1082 : W := mkw 0x0b85c5635c1858d6 0x4170b8ac6b830b1a 0xef87c1e7fc1c79fe 0xfdf0f83cff838f3f

def z1083 : W := mkw 0x0b85c3615c395856 0x0170b86c2b872b0a 0xff87c1e1fc7ff87e 0xfff0f83c3f8fff0f

def z1084 : W := mkw 0x466fbc2be0000000 0x08cdf7857c000000 0x478ffe01e0000002 0x88f1ffc03c000000

def z1085 : W := mkw 0x477fbdffe2400000 0x08eff7bffc480000 0x57ffffffe3e00007 0xeafffffffc7c0000

def z1086 : W := mkw 0x208042001e798ae5 0x4410084003cf315c 0x980000000c739fe0 0x13000000018e73fc

def z1087 : W := mkw 0x047a3898a186a629 0x808f47131430d4c5 0x10783e1803838601 0x020f07c3007070c0

def z1088 : W := mkw 0x066fac2300000000 0x00cdf58460000000 0x47fffe6600000003 0xe8ffffccc0000000

def z1089 : W := mkw 0x0448942b80000000 0x0089128570000000 0x47f9fe7f80000007 0xe8ff3fcff0000000

def z1090 : W := mkw 0x26ef6a003f7f0008 0x84dded4007efe001 0xf7fffe007fff801b 0xfeffffc00ffff003

def z1091 : W := mkw 0x475d8df740000000 0x08ebb1bee8000000 0x47f9cfe600000000 0xc8ff39fcc0000000

def z1092 : W := mkw 0x474d8d6740000000 0x08e9b1ace8000000 0x4789ce6780000006 0xa8f139ccf0000000

def z1093 : W := mkw 0x577fbdffe2c02500 0x0aeff7bffc5804a0 0xdfffffffefe01f87 0xfbfffffffdfc03f0

def z1094 : W := mkw 0x22a76a001d3f0000 0x0454ed4003a7e000 0xf7f7fe001f9f8003 0xfefeffc003f3f000

def z1095 : W := mkw 0x577fbdffe2400100 0x0aeff7bffc480020 0x47ffffffe0600187 0xe8fffffffc0c0030

def z1096 : W := mkw 0x477fbdffe0008229 0x88eff7bffc001045 0x47ffffffe000007f 0xe8fffffffc00000f

def z1097 : W := mkw 0x477fbdffe0802400 0x08eff7bffc100480 0xfffffffff39c667f 0xfffffffffe738ccf

def z1098 : W := mkw 0x4f4d8d6740005856 0x09e9b1ace8000b0a 0x4789ce6600001800 0x88f139ccc0000300

def z1099 : W := mkw 0x0548856700000000 0x00a910ace0000000 0x4789ce6600000000 0x88f139ccc0000000

def z1100 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xf7f9fe001fff8001 0x9eff3fc003fff000

def z1101 : W := mkw 0x0000962b802182a1 0x400012c570043054 0x9809fe7f8c639f87 0xb3013fcff18c73f0

def z1102 : W := mkw 0x019001d018807400 0x0032003a03100e80 0xfff801fe1fe07f85 0xffff003fc3fc0ff0

def z1103 : W := mkw 0x0205942b80000000 0x0040b28570000000 0x478ffe7f80000007 0xe8f1ffcff0000000

def z1104 : W := mkw 0x577fbdffe2c02500 0x0aeff7bffc5804a0 0x47ffffffe3800007 0xe8fffffffc700000

def z1105 : W := mkw 0x064d080000000000 0x00c9a10000000000 0x478fce0000000002 0xe8f1f9c000000000

def z1106 : W := mkw 0x475d8df760000000 0x08ebb1beec000000 0x4789cfe660000000 0x88f139fccc000000

def z1107 : W := mkw 0x477fbdffe0008221 0x08eff7bffc001044 0xdfffffffec739fe7 0xfbfffffffd8e73fc

def z1108 : W := mkw 0x208042001f7f0000 0x0410084003efe000 0x20000000139f8000 0x040000000273f000

def z1109 : W := mkw 0x477f29d461862408 0x88efe53a8c30c481 0xf7ffff80739fe01b 0xfefffff00e73fc03

def z1110 : W := mkw 0x0327a96140000000 0x0064f52c28000000 0x4787ffe1e0000006 0xe8f0fffc3c000000

def z1111 : W := mkw 0x477fbdffe0008221 0x08eff7bffc001044 0x47ffffffe0138067 0xe8fffffffc02700c

def z1112 : W := mkw 0x477fbdffe00082a1 0x48eff7bffc001054 0x47ffffffe0000787 0xe8fffffffc0000f0

def z1113 : W := mkw 0x066f380880000000 0x00cde70110000000 0x47fffe1980000007 0xe8ffffc330000000

def z1114 : W := mkw 0x0548956f80000000 0x00a912adf0000000 0x4789fe7f80000007 0xa8f13fcff0000000

def z1115 : W := mkw 0x77ff29d47bce7500 0x0effe53a8f79cea0 0x67f60180738c6000 0x4cfec0300e718c00

def z1116 : W := mkw 0x411095ffe080a629 0x882212bffc1014c5 0x000001ffe0000604 0x0000003ffc0000c0

def z1117 : W := mkw 0x477fbdffe1068229 0x88eff7bffc20d045 0x47ffffffe0038007 0xe8fffffffc007000

def z1118 : W := mkw 0x477fbdffe1862400 0x08eff7bffc30c480 0xfffffffff39fe607 0xfffffffffe73fcc0

def z1119 : W := mkw 0x467f3c9ea186a629 0x88cfe793d430d4c5 0xf7fffe1e139f8603 0xfeffffc3c273f0c0

def z1120 : W := mkw 0x002220000186a629 0x800444000030d4c5 0xb8763181f39fe67f 0x770ec6303e73fccf

def z1121 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0xfff801ff9ff07fe7 0xffff003ff3fe0ffc

def z1122 : W := mkw 0x067fbcbba186a629 0x80cff7977430d4c5 0xfffffffff39fe67f 0xfffffffffe73fccf

def z1123 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0xb87631f9ff9ffe7f 0xf70ec63f3ff3ffcf

def z1124 : W := mkw 0x6227fe2be53f8ae5 0x4c44ffc57ca7f15c 0x0007fe01e01f8062 0x0000ffc03c03f00c

def z1125 : W := mkw 0x001000900186a629 0x800200120030d4c5 0xb8760199f39fe67f 0x770ec0333e73fccf

def z1126 : W := mkw 0x075d09d400000000 0x00eba13a80000000 0x47f9cffe00000005 0xe8ff39ffc0000000

def z1127 : W := mkw 0x1dd801d45ac07512 0x03bb003a8b580ea2 0xfff801fe7fe07f9d 0xffff003fcffc0ff3

def z1128 : W := mkw 0x0a85c0215c180856 0x0150b8042b83010a 0xef87c181fc1c607e 0xfdf0f8303f838c0f

def z1129 : W := mkw 0x28b27298bffffe7f 0x85164e5317ffffcf 0xb8763199fffffe7f 0x770ec6333fffffcf

def z1130 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xf7f7fe00139f8003 0x7efeffc00273f000

def z1131 : W := mkw 0x0032349aa186a6a9 0xc00646935430d4d5 0xb876319ff39fe7ff 0x770ec633fe73fcff

def z1132 : W := mkw 0x208042001e7908c4 0x4410084003cf2118 0x000000000c601980 0x00000000018c0330

def z1133 : W := mkw 0x477fbdffe00008c4 0x48eff7bffc000118 0x47ffffffe0001987 0xe8fffffffc000330

def z1134 : W := mkw 0x0000420004318ae5 0x400008400086315c 0x9809fe7e0c739fe7 0xb3013fcfc18e73fc

def z1135 : W := mkw 0x108042001ff7ffed 0xc210084003fefffd 0xb80000001ffffff8 0x1700000003ffffff

def z1136 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x47ffff9fe0000003 0x48fffff3fc000000

def z1137 : W := mkw 0x477fbdffe186a629 0x88eff7bffc30d4c5 0x57f9fe7e03838601 0x8aff3fcfc07070c0

def z1138 : W := mkw 0x208042001f7f0000 0x0410084003efe000 0xb00030001fff8003 0x3600060003fff000

def z1139 : W := mkw 0x266f2800010e0000 0x04cde5000021c000 0x47fffe00000c0003 0xe8ffffc000018000

def z1140 : W := mkw 0x0b85014058085012 0x0170a0280b010a02 0x6f860181f00c607c 0x4df0c0303e018c0f

def z1141 : W := mkw 0x477fadf760000000 0x08eff5beec000000 0x47f9ce6600000000 0x88ff39ccc0000000

def z1142 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x47f9ffffe0000005 0x88ff3ffffc000000

def z1143 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0xff87f1e1fc1ff87f 0xfff0fe3c3f83ff0f

def z1144 : W := mkw 0x477fbdffe1060000 0x08eff7bffc20c000 0x57ffffffe3838007 0xeafffffffc707000

def z1145 : W := mkw 0x24c842001f7f0000 0x0499084003efe000 0xf7f9fe001fff8003 0xfeff3fc003fff000

def z1146 : W := mkw 0x4000d62be4318ae5 0x48001ac57c86315c 0x9809fe7fec739fe7 0xb3013fcffd8e73fc

def z1147 : W := mkw 0x457abdffa0000000 0x08af57bff4000000 0x47f9ffff80000007 0xe8ff3ffff0000000

def z1148 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0xfff8007e1fe07f81 0x9fff000fc3fc0ff0

def z1149 : W := mkw 0x209042901fff2400 0x0412085203ffe480 0xb87001981fffe605 0x770e003303fffcc0

def z1150 : W := mkw 0x66ef6a007f7f0000 0x0cdded400fefe000 0xf7fffe007fff8003 0xfeffffc00ffff000

def z1151 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xffffff801fffe007 0xfffffff003fffc00

def z1152 : W := mkw 0x4337bdfbe0000000 0x0866f7bf7c000000 0x47f7fff9e0000007 0xe8feffff3c000000

def z1153 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x0800007f8c601fe4 0x0100000ff18c03fc

def z1154 : W := mkw 0x474d8d6740000000 0x08e9b1ace8000000 0x4789ce660c601980 0x88f139ccc18c0330

def z1155 : W := mkw 0x477fadf760000000 0x08eff5beec000000 0x47f7cf8060000000 0x48fef9f00c000000

def z1156 : W := mkw 0x067f289021862408 0x80cfe5120430c481 0x67ffff80738c601b 0xecfffff00e718c03

def z1157 : W := mkw 0x577fbdffe2c07500 0x0aeff7bffc580ea0 0x5fffffffe3e07f87 0xebfffffffc7c0ff0

def z1158 : W := mkw 0x477fbdffe0008221 0x08eff7bffc001044 0x4fffffffe0000667 0xe9fffffffc0000cc

def z1159 : W := mkw 0x00223008a1068229 0x800446011420d045 0xb8763181f39fe07f 0x770ec6303e73fc0f

def z1160 : W := mkw 0x091095fbe080feff 0xc12212bf7c101fdf 0x080001ffe0007ffc 0x0100003ffc000fff

def z1161 : W := mkw 0x466f280060000000 0x08cde5000c000000 0x47fffe0060000003 0xe8ffffc00c000000

def z1162 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0xef8fffe1fc1c787f 0xfdf1fffc3f838f0f

def z1163 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0xf7f8007e1fe01f81 0xfeff000fc3fc03f0

def z1164 : W := mkw 0x475d8df740802400 0x08ebb1bee8100480 0xfff9cffe13806605 0xffff39ffc2700cc0

def z1165 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xe7f7fe001f9f8002 0xfcfeffc003f3f000

def z1166 : W := mkw 0x0000000000000000 0x0000000000000000 0x9009fe0000138003 0xb2013fc000027000

def z1167 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0xb8763181f39fe67a 0x570ec6303e73fccf

def z1168 : W := mkw 0x2eef6a001f7f5856 0x05dded4003efeb0a 0xf7fffe001fff9803 0xfeffffc003fff300

def z1169 : W := mkw 0x577fbdffe080f729 0x8aeff7bffc101ee5 0x4fffffffe0007fff 0xe9fffffffc000fff

def z1170 : W := mkw 0x30b262901fff7500 0x06164c5203ffeea0 0xb87631981fffff87 0x770ec63303fffff0

def z1171 : W := mkw 0x3fff29d45bce7512 0x07ffe53a8b79cea2 0x67f60180738c6018 0x4cfec0300e718c03

def z1172 : W := mkw 0x477fbdffe0802408 0x88eff7bffc100481 0x47ffffffe000601f 0xe8fffffffc000c03

def z1173 : W := mkw 0x26ef2a001b6f0000 0x04dde540036de000 0x77fffe0013ef8003 0xeeffffc0027df000

def z1174 : W := mkw 0x266f280003460000 0x04cde5000068c000 0x47fffe0003800003 0xe8ffffc000700000

def z1175 : W := mkw 0x474d8d6740000000 0x08e9b1ace8000000 0x4781ce0000000000 0x08f039c000000000

def z1176 : W := mkw 0x1dd801d41ac87512 0x03bb003a83590ea2 0xfff801fe1fec7f9d 0xffff003fc3fd8ff3

def z1177 : W := mkw 0x4227bc2be0000000 0x0844f7857c000000 0x4787fe01e0000002 0xe8f0ffc03c000000

def z1178 : W := mkw 0x477fadf761862408 0x88eff5beec30c481 0x67ffcfe6738c6018 0xccfff9fcce718c03

def z1179 : W := mkw 0x0000942b80008221 0x0000128570001044 0x9809fe7f8c739fe7 0xb3013fcff18e73fc

def z1180 : W := mkw 0x208042001f7f8229 0x8410084003eff045 0xb00000001fff8078 0x1600000003fff00f

def z1181 : W := mkw 0x547a3c9ea3c6a729 0x8a8f4793d478d4e5 0x10783e1e03e38781 0x020f07c3c07c70f0

def z1182 : W := mkw 0x266f2a0003670000 0x04cde540006ce000 0xf7fffe0013ff8003 0xfeffffc0027ff000

def z1183 : W := mkw 0x2b85cb615c395856 0x0570b96c2b872b0a 0xef87cfe1fc1c787e 0xfdf0f9fc3f838f0f

def z1184 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x47fffe7e00000003 0xe8ffffcfc0000000

def z1185 : W := mkw 0x347a3a9ca3e7a729 0x868f4753947cf4e5 0x10783e1e03e38781 0x020f07c3c07c70f0

def z1186 : W := mkw 0x008042001c31dae5 0x4010084003863b5c 0xb80000001c73ffe0 0x17000000038e7ffc

def z1187 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x47ffcfffe0000004 0xc8fff9fffc000000

def z1188 : W := mkw 0x208042001f7f0000 0x0410084003efe000 0xb00800001fff8001 0xb601000003fff000

def z1189 : W := mkw 0x208042001f7f0000 0x0410084003efe000 0xb8060181ffffe07e 0x7700c0303ffffc0f

def z1190 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0xfff831fe1ff3ff87 0xffff063fc3fe7ff0

def z1191 : W := mkw 0x074d896140000000 0x00e9b12c28000000 0x478fcfe1e0000006 0xe8f1f9fc3c000000

def z1192 : W := mkw 0x055801d400000000 0x00ab003a80000000 0x47f9fffe00000007 0xe8ff3fffc0000000

def z1193 : W := mkw 0x477fbdffe1068229 0x88eff7bffc20d045 0xeffffffff01fe07f 0xfdfffffffe03fc0f

def z1194 : W := mkw 0x208042001d3f0000 0x0410084003a7e000 0xa00000001c1f8000 0x140000000383f000

def z1195 : W := mkw 0x066f280000000000 0x00cde50000000000 0x47ffce0000000000 0xc8fff9c000000000

def z1196 : W := mkw 0x477fbdffe186aeed 0xc8eff7bffc30d5dd 0xfffffffff39fffff 0xfffffffffe73ffff

def z1197 : W := mkw 0x0b85816158085856 0x0170b02c2b010b0a 0xef8601e1f01c787e 0x7df0c03c3e038f0f

def z1198 : W := mkw 0x477fbdffe186a629 0x88eff7bffc30d4c5 0x67f7ff81f39fe07a 0x4cfefff03e73fc0f

def z1199 : W := mkw 0x0180014018005000 0x0030002803000a00 0xef860181f01c607e 0x7df0c0303e038c0f

def z1200 : W := mkw 0x474d9d6fc0000000 0x08e9b3adf8000000 0x4789ce7f80000004 0x88f139cff0000000

def z1201 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x0809fe7f8c739fe6 0x81013fcff18e73fc

def z1202 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0xdff8007e0fe01f85 0xbbff000fc1fc03f0

def z1203 : W := mkw 0x108042001e71dbe5 0x4210084003ce3b7c 0x980000000c739fe0 0x13000000018e73fc

def z1204 : W := mkw 0x477fbdffe1862408 0x88eff7bffc30c481 0xfffffffff38c661f 0xfffffffffe718cc3

def z1205 : W := mkw 0x477fbdffe1862408 0x88eff7bffc30c481 0x47ffffffe3800007 0xe8fffffffc700000

def z1206 : W := mkw 0x067f289000802400 0x00cfe51200100480 0xffffff9813806607 0xfffffff302700cc0

def z1207 : W := mkw 0x0000c22104310844 0x0000184420862108 0x9809fe7f8c739fe7 0xb3013fcff18e73fc

def z1208 : W := mkw 0x20905298bfffa629 0x84120a5317fff4c5 0xb8000199ffffe67c 0x170000333ffffccf

def z1209 : W := mkw 0x4337bdfbe186a629 0x8866f7bf7c30d4c5 0xfff7fff9f39fe67f 0xfffeffff3e73fccf

def z1210 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0xd7ffffffe0138007 0xfafffffffc027000

def z1211 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0xff87c1f9fc1c7e7f 0xfff0f83f3f838fcf

def z1212 : W := mkw 0x208042001fff2400 0x0410084003ffe480 0xb80000001fffe600 0x1700000003fffcc0

def z1213 : W := mkw 0x467f3c9ea0000000 0x08cfe793d4000000 0x47ffff9fe0000007 0xe8fffff3fc000000

def z1214 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0x6787c1e1fc1c787a 0xccf0f83c3f838f0f

def z1215 : W := mkw 0x464d8c2340000000 0x08c9b18468000000 0x4789ce0000000000 0x88f139c000000000

def z1216 : W := mkw 0x0337b5fbe186a629 0x8066f6bf7c30d4c5 0xfffffffff39fe67f 0xfffffffffe73fccf

def z1217 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0x6787c1e1f01c607e 0xecf0f83c3e038c0f

def z1218 : W := mkw 0x288042001f7f5856 0x0510084003efeb0a 0xb00000001fff9800 0x1600000003fff300

def z1219 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0xcfffffffec001807 0xf9fffffffd800300

def z1220 : W := mkw 0x308042001fff7500 0x0610084003ffeea0 0xb00000001fffe000 0x1600000003fffc00

def z1221 : W := mkw 0x067f3898a186a629 0x80cfe7131430d4c5 0x57fffe1803838603 0xeaffffc3007070c0

def z1222 : W := mkw 0x477f29d460000000 0x08efe53a8c000000 0x47ffcf8060000000 0xc8fff9f00c000000

def z1223 : W := mkw 0x477fbdffe186a629 0x88eff7bffc30d4c5 0x57ffffffe39f867f 0xeafffffffc73f0cf

def z1224 : W := mkw 0x14c800001ac07500 0x0299000003580ea0 0xfff8007e1fe07f85 0xffff000fc3fc0ff0

def z1225 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0x67fffe00139f8003 0xecffffc00273f000

def z1226 : W := mkw 0x477fbdffe0802400 0x08eff7bffc100480 0x4fffffffe0006607 0xe9fffffffc000cc0

def z1227 : W := mkw 0x677fbdffe3460000 0x0ceff7bffc68c000 0x47ffffffe3800007 0xe8fffffffc700000

def z1228 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x47ffffffe01c007f 0xe8fffffffc03800f

def z1229 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x478fffffe0000006 0x88f1fffffc000000

def z1230 : W := mkw 0x038541401c185000 0x0070a82803830a00 0xef87c1e1fc1c787e 0xfdf0f83c3f838f0f

def z1231 : W := mkw 0x4f4d8d6740005856 0x09e9b1ace8000b0a 0x4f89cfe7e000787c 0x89f139fcfc000f0f

def z1232 : W := mkw 0x474d094440000000 0x08e9a12888000000 0x4789ce0000000000 0x88f139c000000000

def z1233 : W := mkw 0x208042001fffaeed 0xc410084003fff5dd 0xb80000001ffffff8 0x1700000003ffffff

def z1234 : W := mkw 0x147a369ea3e7a7a9 0xc28f46d3d47cf4f5 0x10783e1e03e38781 0x020f07c3c07c70f0

def z1235 : W := mkw 0x0b85c3615c395856 0x0170b86c2b872b0a 0xef8fcfe1fc7c787e 0xfdf1f9fc3f8f8f0f

def z1236 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0x57fffe000fff8003 0x8affffc001fff000

def z1237 : W := mkw 0x288042001f7f0856 0x0510084003efe10a 0xb00000001fff8078 0x1600000003fff00f

def z1238 : W := mkw 0x574d8d6740005100 0x0ae9b1ace8000a20 0x4789ce6600001980 0x88f139ccc0000330

def z1239 : W := mkw 0x066f6a0005370000 0x00cded4000a6e000 0xf7fffe001fff8003 0xfeffffc003fff000

def z1240 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0xb87e319ff3ffe7ff 0x770fc633fe7ffcff

def z1241 : W := mkw 0x055843d404318ae5 0x40ab087a8086315c 0xdff801fe0c739fe5 0xfbff003fc18e73fc

def z1242 : W := mkw 0x077f39dca0000000 0x00efe73b94000000 0x47ffffffe0000007 0xe8fffffffc000000

def z1243 : W := mkw 0x477fbdffe1060000 0x08eff7bffc20c000 0x47ffffffe01f8007 0xe8fffffffc03f000

def z1244 : W := mkw 0x076fa96140000000 0x00edf52c28000000 0x47fffe6000000003 0xe8ffffcc00000000

def z1245 : W := mkw 0x477fbdffe1862408 0x88eff7bffc30c481 0xeffffffff39c607f 0xfdfffffffe738c0f

def z1246 : W := mkw 0x288042001f7f5012 0x0510084003efea02 0xb00000001fffe018 0x1600000003fffc03

def z1247 : W := mkw 0x1190d7ff9ef1ffe5 0x42321afff3de3ffc 0xb80001ff9ff3ffe4 0x1700003ff3fe7ffc

def z1248 : W := mkw 0x467f3c9ea186a629 0x88cfe793d430d4c5 0xffffff9ff39fe67f 0xfffffff3fe73fccf

def z1249 : W := mkw 0x076f294040000000 0x00ede52808000000 0x47ffff8060000003 0xe8fffff00c000000

def z1250 : W := mkw 0x474d8d6740000000 0x08e9b1ace8000000 0x47f9ce6600000001 0xe8ff39ccc0000000

def z1251 : W := mkw 0x477fbdffe0000844 0x08eff7bffc000108 0x4fffffffe0001867 0xe9fffffffc00030c

def z1252 : W := mkw 0x474d9d6fc0000000 0x08e9b3adf8000000 0x478fffffe0000007 0xe8f1fffffc000000

def z1253 : W := mkw 0x0a27f62be53f8aff 0xc144fec57ca7f15f 0x0007fe01e01f807a 0x0000ffc03c03f00f

def z1254 : W := mkw 0x511095ffe080f729 0x8a2212bffc101ee5 0x080001ffe0007ffc 0x0100003ffc000fff

def z1255 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0xb87fff99f39fe67f 0xf70ffff33e73fccf

def z1256 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xf7fffe01ffff807b 0xfeffffc03ffff00f

def z1257 : W := mkw 0x064d080000000000 0x00c9a10000000000 0x4789fe0000000003 0xa8f13fc000000000

def z1258 : W := mkw 0x4327bd6be0000000 0x0864f7ad7c000000 0x4787fe61e0000002 0x88f0ffcc3c000000

def z1259 : W := mkw 0x467f3c9ea0000000 0x08cfe793d4000000 0x47f9fe1e00000001 0x88ff3fc3c0000000

def z1260 : W := mkw 0x04ea62001f770000 0x009d4c4003eee000 0xf7fffe001fff8003 0xfeffffc003fff000

def z1261 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0xfffe01fe1ffc7f87 0xffffc03fc3ff8ff0

def z1262 : W := mkw 0x477fbdffe0005000 0x08eff7bffc000a00 0x4fffffffe0007807 0xe9fffffffc000f00

def z1263 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0xfff801fe1ffc7ffd 0xffff003fc3ff8fff

def z1264 : W := mkw 0x30b27298bffff729 0x86164e5317fffee5 0xb8763199ffffffff 0x770ec6333fffffff

def z1265 : W := mkw 0x088042001dbffeff 0xc110084003b7ffdf 0xb80000001ffffff8 0x1700000003ffffff

def z1266 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xf7ffff81ffff8007 0xfefffff03ffff000

def z1267 : W := mkw 0x477fbdffe080aeed 0xc8eff7bffc1015dd 0x4fffffffe0007fff 0xe9fffffffc000fff

def z1268 : W := mkw 0x077fb9f9e186a629 0x80eff73f3c30d4c5 0xfffffff9f39fe67f 0xffffffff3e73fccf

def z1269 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0x6ff801fe1fe07f84 0xcdff003fc3fc0ff0

def z1270 : W := mkw 0x474d9d6fc0008221 0x08e9b3adf8001044 0xdf89fe7f80138667 0xbbf13fcff00270cc

def z1271 : W := mkw 0x119001d41ac07500 0x0232003a83580ea0 0x080001fe0c607f84 0x0100003fc18c0ff0

def z1272 : W := mkw 0x208042001f7f0000 0x0410084003efe000 0xb808007e1fff9f85 0xb701000fc3fff3f0

def z1273 : W := mkw 0x047a3098a3c6a629 0x808f46131478d4c5 0x1078301803e38601 0x020f0603007c70c0

def z1274 : W := mkw 0x067fbcbba0000000 0x00cff79774000000 0x47ffffffe0000007 0xe8fffffffc000000

def z1275 : W := mkw 0x26ef2a001b670000 0x04dde540036ce000 0xf7fffe001fe38003 0xfeffffc003fc7000

def z1276 : W := mkw 0x066fa82140000000 0x00cdf50428000000 0x47fffe01e0000003 0xe8ffffc03c000000

def z1277 : W := mkw 0x477f29d460000000 0x08efe53a8c000000 0x47fffffe60000007 0xe8ffffffcc000000

def z1278 : W := mkw 0x477fbdffe186a629 0x88eff7bffc30d4c5 0x5fffffffe383e67f 0xebfffffffc707ccf

def z1279 : W := mkw 0x088042001c39daf7 0x4110084003873b5e 0xa80000001c1ff878 0x150000000383ff0f

def z1280 : W := mkw 0x266f6a00053f0000 0x04cded4000a7e000 0xf7fffe00139f8003 0xfeffffc00273f000

def z1281 : W := mkw 0x477fadf760000000 0x08eff5beec000000 0x47ffffe660000003 0xe8fffffccc000000

def z1282 : W := mkw 0x0b85014058085012 0x0170a0280b010a02 0xef8601e1fc1c787e 0xfdf0c03c3f838f0f

def z1283 : W := mkw 0x20b262903fff2408 0x84164c5207ffe481 0xb07601807fffe018 0x560ec0300ffffc03

def z1284 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x4fffffffe000607f 0xe9fffffffc000c0f

def z1285 : W := mkw 0x0b85c7635c3958d6 0x4170b8ec6b872b1a 0xff8fffe7fc7ff9ff 0xfff1fffcff8fff3f

def z1286 : W := mkw 0x4337bdffe0000000 0x0866f7bffc000000 0x4787ffffe0000006 0xe8f0fffffc000000

def z1287 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x47fffffe60000001 0xc8ffffffcc000000

def z1288 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0x6f87c1e1fc0c787c 0xcdf0f83c3f818f0f

def z1289 : W := mkw 0x0305014040000000 0x0060a02808000000 0xef860181f01c607e 0x7df0c0303e038c0f

def z1290 : W := mkw 0x20b27298bf7f0000 0x04164e5317efe000 0xb0763199ffff8007 0x760ec6333ffff000

def z1291 : W := mkw 0x057ab5ffa186a629 0x80af56bff430d4c5 0xfffffffff39fe67f 0xfffffffffe73fccf

def z1292 : W := mkw 0x474d9d6fc0008ae5 0x48e9b3adf800115c 0x4f89ce7f80001fe4 0x89f139cff00003fc

def z1293 : W := mkw 0x388042001fff7d56 0x0710084003ffefaa 0xb80000001ffffff8 0x1700000003ffffff

def z1294 : W := mkw 0x0b85c7635c3958d6 0x4170b8ec6b872b1a 0xef87cfe1fc1c787e 0xfdf0f9fc3f838f0f

def z1295 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0xfff801ffffe07ffd 0xffff003ffffc0fff

def z1296 : W := mkw 0x474d8d6740000000 0x08e9b1ace8000000 0x4789fe6600000003 0xa8f13fccc0000000

def z1297 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0x77fffe001fef8001 0xceffffc003fdf000

def z1298 : W := mkw 0x474d8d6740000000 0x08e9b1ace8000000 0x4789cfe7e0000004 0x88f139fcfc000000

def z1299 : W := mkw 0x0100014000000000 0x0020002800000000 0xef8601e1f01c607e 0xfdf0c03c3e038c0f

def z1300 : W := mkw 0x4327bd6be0000000 0x0864f7ad7c000000 0x478fffffe0000007 0xe8f1fffffc000000

def z1301 : W := mkw 0x055801d400802400 0x00ab003a80100480 0xfff801fe1fe07f85 0xffff003fc3fc0ff0

def z1302 : W := mkw 0x474d9d6fc0000000 0x08e9b3adf8000000 0x4789fe7e00000001 0x88f13fcfc0000000

def z1303 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0xb879fe7f9ff39fe7 0xf70f3fcff3fe73fc

def z1304 : W := mkw 0x477fbdffe0008ae5 0x48eff7bffc00115c 0xdfffffffe0139fe7 0xfbfffffffc0273fc

def z1305 : W := mkw 0x477fbdffe1060008 0x88eff7bffc20c001 0x47ffffffe00c001f 0xe8fffffffc018003

def z1306 : W := mkw 0x067f289000000000 0x00cfe51200000000 0x47ffff9800000007 0xe8fffff300000000

def z1307 : W := mkw 0x1080942b9ac07500 0x0210128573580ea0 0xb809fe7f9fe07f87 0xb7013fcff3fc0ff0

def z1308 : W := mkw 0x466fbc2be0000000 0x08cdf7857c000000 0x47f7fe01e0000002 0x48feffc03c000000

def z1309 : W := mkw 0x076f294000000000 0x00ede52800000000 0x47ffffe000000007 0xe8fffffc00000000

def z1310 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0xef87c1fffc1c7ffe 0xfdf0f83fff838fff

def z1311 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0xdfffffffe0000607 0xfbfffffffc0000c0

def z1312 : W := mkw 0x467fbcbfe0000000 0x08cff797fc000000 0x47fffe1fe0000003 0xe8ffffc3fc000000

def z1313 : W := mkw 0x574d8d6742400100 0x0ae9b1ace8480020 0x4789ce6600600180 0x88f139ccc00c0030

def z1314 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0xfff9fffe1fe07f87 0xffff3fffc3fc0ff0

def z1315 : W := mkw 0x308042001ef97500 0x0610084003df2ea0 0xb80000001fe07f80 0x1700000003fc0ff0

def z1316 : W := mkw 0x477fbdffe0000000 0x08eff7bffc000000 0x47f7ffe1e0000006 0xe8fefffc3c000000

def z1317 : W := mkw 0x0205000000000000 0x0040a00000000000 0xe787c000101c0002 0xfcf0f80002038000

def z1318 : W := mkw 0x066ffe2b85378ae5 0x40cdffc570a6f15c 0xfffffe7f9fff9fe7 0xffffffcff3fff3fc

def z1319 : W := mkw 0x008042001c398ae5 0x401008400387315c 0xb80000001c7f9fe0 0x17000000038ff3fc

def z1320 : W := mkw 0x208042001e790000 0x0410084003cf2000 0x900000000c738000 0x12000000018e7000

def z1321 : W := mkw 0x308042001fffffe5 0x4610084003fffffc 0xb80000001fffffe0 0x1700000003fffffc

def z1322 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0xa8763181f39fe07e 0x750ec6303e73fc0f

def z1323 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0xef87c181fc1c787a 0x5df0f8303f838f0f

def z1324 : W := mkw 0x26ef6a001f7f0000 0x04dded4003efe000 0xfffffe001fff9f83 0xffffffc003fff3f0

def z1325 : W := mkw 0x20a262001f7f0000 0x04144c4003efe000 0xb07600001fff8000 0x560ec00003fff000

def z1326 : W := mkw 0x0b85c1615c185856 0x0170b82c2b830b0a 0xef87c181f01c607e 0x7df0f8303e038c0f

def z1327 : W := mkw 0x208042001e790000 0x0410084003cf2000 0xa00000001c7c0000 0x14000000038f8000

def z1328 : W := mkw 0x476fbd6be0000000 0x08edf7ad7c000000 0x47ffffe1e0000007 0xe8fffffc3c000000

def z1329 : W := mkw 0x474d8d6740000000 0x08e9b1ace8000000 0x478fce6600000002 0xe8f1f9ccc0000000

def z1330 : W := mkw 0x0227280001060000 0x0044e5000020c000 0x0007fe00001f8002 0x0000ffc00003f000

def z1331 : W := mkw 0x055885f700000000 0x00ab10bee0000000 0x47f9cffe00000005 0xe8ff39ffc0000000

def z1332 : W := mkw 0x2eef6a001f7f5012 0x05dded4003efea02 0xf7fffe001fffe01b 0xfeffffc003fffc03

def z1333 : W := mkw 0x477fbdffe080a629 0x88eff7bffc1014c5 0xdfffffffe013e67f 0xfbfffffffc027ccf

def z1334 : W := mkw 0x477fbdffe0802400 0x08eff7bffc100480 0x67fffffff3806007 0xecfffffffe700c00

def z1335 : W := mkw 0x2eef6a001f7f0856 0x05dded4003efe10a 0xf7fffe001fff807b 0xfeffffc003fff00f

def z1336 : W := mkw 0x088052089c39daf7 0x41100a4113873b5e 0xb8063199fc7fffff 0x7700c6333f8fffff

def z1337 : W := mkw 0x0180c1611c105844 0x0030182c23820b08 0xef87c1e1fc1c787e 0xfdf0f83c3f838f0f

def z1338 : W := mkw 0x55d801d47ac07500 0x0abb003a8f580ea0 0xfff801fe7fe07f85 0xffff003fcffc0ff0

def z1339 : W := mkw 0x066f280000000000 0x00cde50000000000 0xefffff81f01c607f 0xfdfffff03e038c0f

def z1340 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0xb80ffe7f9c7f9fe7 0xf701ffcff38ff3fc

def z1341 : W := mkw 0x308042001f7f5100 0x0610084003efea20 0xb00000001fff9980 0x1600000003fff330

def z1342 : W := mkw 0x2227fe2ba53f8aed 0xc444ffc574a7f15d 0x0007fe01e01f807a 0x0000ffc03c03f00f

def z1343 : W := mkw 0x066fa82100000000 0x00cdf50420000000 0x47fffe6180000007 0xe8ffffcc30000000

def z1344 : W := mkw 0x0032209021862408 0x800644120430c481 0xb8763181f39fe07f 0x770ec6303e73fc0f

def z1345 : W := mkw 0x288042001ffffe7f 0x8510084003ffffcf 0xb80000001ffffe78 0x1700000003ffffcf

def z1346 : W := mkw 0x0b85c7635c3958d6 0x4170b8ec6b872b1a 0xff8fcffffc7c7fff 0xfff1f9ffff8f8fff

def z1347 : W := mkw 0x6fcdcf675e795856 0x0df9b9ecebcf2b0a 0x4789ce660c601800 0x88f139ccc18c0300

def z1348 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x9009fe7e0c739f83 0xb2013fcfc18e73f0

def z1349 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0xb0763181f39fe07b 0x760ec6303e73fc0f

def z1350 : W := mkw 0x474d8d67400008c4 0x48e9b1ace8000118 0x4789ce6600001980 0x88f139ccc0000330

def z1351 : W := mkw 0x0285000018080000 0x0050a00003010000 0xef860181f01c607e 0x7df0c0303e038c0f

def z1352 : W := mkw 0x288042001e795856 0x0510084003cf2b0a 0xa80000001c7c7878 0x15000000038f8f0f

def z1353 : W := mkw 0x067f3898a0000000 0x00cfe71314000000 0x47fffe1800000003 0xe8ffffc300000000

def z1354 : W := mkw 0x0337b5fbe0000000 0x0066f6bf7c000000 0x47ffffffe0000007 0xe8fffffffc000000

def z1355 : W := mkw 0x288042001f7fdaf7 0x4510084003effb5e 0xb80000001ffffff8 0x1700000003ffffff

def z1356 : W := mkw 0x064d080000000000 0x00c9a10000000000 0x47f9ce0000000001 0xe8ff39c000000000

def z1357 : W := mkw 0x208042001fffa629 0x8410084003fff4c5 0xb00000001fff8600 0x1600000003fff0c0

def z1358 : W := mkw 0x066f3808a1068229 0x80cde7011420d045 0x47fffe01e01f807b 0xe8ffffc03c03f00f

def z1359 : W := mkw 0x476fbd6fe1068229 0x88edf7adfc20d045 0x478ffe67e01f807a 0x88f1ffccfc03f00f

def z1360 : W := mkw 0x0000d62b84318ae5 0x40001ac57086315c 0x980ffe7fec7f9fff 0xb301ffcffd8ff3ff

def z1361 : W := mkw 0x477fbdffe186a629 0x88eff7bffc30d4c5 0xdfffffffe3938667 0xfbfffffffc7270cc

def z1362 : W := mkw 0x476fbd6fc0000000 0x08edf7adf8000000 0x47fffe7f80000007 0xe8ffffcff0000000

def z1363 : W := mkw 0x0022300881068221 0x000446011020d044 0xb8763199f39fe67f 0x770ec6333e73fccf

def z1364 : W := mkw 0x00323098a186a629 0x800646131430d4c5 0xb87e3199ffffe67f 0xf70fc6333ffffccf

def z1365 : W := mkw 0x477fa9f560000000 0x08eff53eac000000 0x47ffffe1e0000007 0xe8fffffc3c000000

def z1366 : W := mkw 0x15d801d41ac07500 0x02bb003a83580ea0 0xfffe01ffffe07f87 0xffffc03ffffc0ff0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z7,z4,z8,z6]),(0,[z1,z2,z9,z10,z4,z8,z6]),(0,[z1,z2,z11,z3,z4,z8,z12]),(0,[z1,z2,z13,z3,z4,z8,z6])],[(0,[z1,z2,z3,z14,z4,z8,z6]),(0,[z1,z2,z3,z4,z15,z8,z16]),(0,[z17,z1,z2,z11,z3,z4,z8]),(0,[z18,z1,z2,z4,z19,z8,z6]),(0,[z1,z2,z11,z3,z4,z8,z6])],[(0,[z20,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z21,z4,z22,z8])],[(0,[z1,z2,z23,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z24,z8,z6]),(0,[z1,z2,z3,z25,z4,z8,z6])],[(0,[z1,z26,z2,z27,z4,z8,z6]),(0,[z1,z28,z2,z3,z4,z8,z6]),(0,[z1,z2,z29,z3,z4,z8,z6]),(0,[z1,z2,z11,z3,z30,z4,z8]),(0,[z31,z1,z2,z3,z4,z22,z8]),(0,[z1,z2,z3,z4,z8,z6,z32])],[(0,[z1,z2,z33,z3,z4,z8,z6]),(0,[z1,z2,z3,z34,z4,z8,z6]),(0,[z1,z2,z3,z4,z35,z8,z6])],[(0,[z1,z2,z36,z3,z4,z8,z6]),(0,[z37,z1,z2,z3,z4,z8,z6]),(0,[z38,z1,z2,z3,z4,z22,z8]),(0,[z1,z2,z3,z4,z39,z8,z6]),(0,[z1,z2,z40,z4,z19,z8,z6]),(1,[z1,z2,z41,z4,z8,z12]),(0,[z42,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z43,z3,z4,z8,z6])]],
   [[(0,[z44,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z45,z8,z6]),(0,[z1,z2,z3,z4,z8,z46,z47]),(0,[z1,z2,z48,z11,z3,z4,z8]),(0,[z1,z2,z11,z40,z3,z4,z8])],[(0,[z1,z2,z3,z4,z8,z6,z49]),(0,[z1,z2,z50,z3,z4,z8,z6]),(0,[z1,z2,z51,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z52,z8,z6]),(0,[z1,z2,z3,z53,z4,z8,z6]),(0,[z1,z2,z3,z54,z4,z8,z6]),(0,[z1,z2,z55,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z56,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z57])],[(1,[z1,z2,z58,z3,z4,z8]),(0,[z1,z59,z2,z3,z21,z8,z6]),(0,[z1,z2,z11,z3,z4,z8,z60]),(0,[z1,z2,z61,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z62,z8,z6])],[(0,[z2,z3,z63,z4,z64,z8,z6]),(0,[z1,z2,z40,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z8,z65,z6])],[(0,[z1,z2,z3,z66,z4,z8,z6]),(0,[z1,z67,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z68,z8,z6]),(0,[z1,z2,z61,z3,z10,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z69]),(0,[z1,z2,z11,z3,z4,z8,z70])],[(0,[z71,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z72])],[(1,[z1,z2,z9,z10,z8,z6]),(0,[z1,z73,z2,z3,z4,z8,z6])],[(0,[z74,z1,z2,z3,z4,z8,z75]),(0,[z1,z2,z3,z4,z8,z6,z76]),(0,[z1,z2,z3,z4,z77,z8,z6])]],
   [[(0,[z78,z1,z2,z11,z3,z4,z8]),(0,[z74,z1,z2,z3,z79,z4,z8]),(0,[z1,z2,z3,z4,z19,z60,z6]),(0,[z1,z2,z80,z3,z4,z8,z47]),(0,[z1,z2,z3,z4,z81,z8,z47]),(0,[z1,z2,z82,z3,z4,z8,z6])],[(0,[z1,z2,z83,z3,z4,z22,z8]),(0,[z84,z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z85,z3,z4,z22,z8]),(1,[z1,z2,z3,z86,z4,z8]),(0,[z1,z26,z2,z48,z4,z8,z6]),(0,[z1,z2,z87,z3,z4,z22,z8]),(0,[z1,z59,z2,z3,z4,z22,z8]),(0,[z1,z2,z88,z3,z4,z8,z6])],[(0,[z1,z2,z3,z27,z4,z8,z47]),(0,[z1,z2,z3,z89,z4,z8,z6])],[(0,[z18,z1,z2,z27,z4,z8,z6]),(0,[z90,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z19,z91,z6]),(0,[z1,z2,z55,z3,z4,z92,z6]),(0,[z1,z2,z3,z4,z8,z6,z93]),(1,[z1,z2,z3,z4,z94,z8]),(0,[z1,z2,z95,z3,z4,z22,z8])],[(0,[z1,z26,z2,z85,z4,z8,z6]),(0,[z96,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z97,z4,z8,z6]),(0,[z98,z1,z2,z11,z3,z4,z8])],[(0,[z1,z2,z9,z3,z99,z8,z6]),(0,[z100,z1,z2,z3,z4,z8,z6])],[(0,[z1,z101,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z102,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z103,z6])],[(0,[z1,z104,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z105,z6]),(0,[z1,z2,z106,z3,z4,z8,z6]),(0,[z1,z2,z10,z4,z99,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z107])]],
   [[(0,[z1,z2,z85,z4,z8,z108,z6]),(0,[z1,z2,z3,z4,z8,z6,z109]),(0,[z1,z2,z3,z4,z110,z8,z6]),(0,[z1,z2,z3,z4,z8,z111,z6]),(0,[z1,z59,z2,z3,z4,z8,z76]),(0,[z1,z2,z3,z4,z112,z8,z6]),(0,[z1,z2,z3,z113,z4,z8,z6]),(0,[z1,z2,z114,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z92,z6]),(0,[z1,z2,z3,z4,z8,z6,z115])],[(0,[z17,z0,z2,z3,z4,z8,z6]),(1,[z1,z2,z116,z3,z8,z6]),(1,[z18,z1,z27,z4,z8,z6]),(0,[z1,z2,z3,z4,z117,z8,z6]),(0,[z1,z118,z2,z11,z3,z4,z8]),(0,[z1,z2,z3,z119,z4,z8,z16]),(0,[z1,z2,z3,z4,z120,z8,z6]),(1,[z1,z2,z3,z4,z8,z121])],[(0,[z1,z2,z3,z4,z8,z122,z6]),(0,[z1,z2,z123,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z16,z124]),(0,[z1,z2,z3,z125,z4,z8,z6]),(0,[z1,z2,z126,z3,z4,z8,z6])],[(0,[z1,z127,z2,z3,z4,z22,z8]),(0,[z1,z2,z3,z4,z8,z16,z128]),(0,[z1,z2,z3,z4,z8,z129,z6]),(1,[z1,z2,z88,z3,z8,z93])],[(0,[z130,z1,z2,z11,z3,z4,z8]),(0,[z38,z1,z2,z88,z3,z4,z8]),(0,[z131,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z132,z8,z6]),(0,[z1,z2,z133,z3,z4,z8,z6]),(0,[z1,z2,z3,z134,z4,z8,z47]),(0,[z1,z2,z135,z3,z4,z8,z6])],[(0,[z1,z2,z136,z3,z4,z8,z6]),(0,[z137,z1,z2,z3,z4,z8,z6]),(0,[z138,z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z139,z6]),(0,[z140,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z141,z47]),(0,[z1,z2,z55,z4,z8,z70,z6]),(0,[z1,z2,z3,z4,z8,z142,z6])],[(0,[z143,z1,z2,z3,z4,z8,z6]),(0,[z1,z144,z127,z3,z4,z8,z6]),(0,[z74,z1,z2,z3,z4,z8,z6]),(0,[z1,z118,z2,z3,z4,z8,z145]),(0,[z146,z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z70,z16])],[(0,[z127,z2,z83,z3,z4,z8,z6]),(0,[z2,z85,z3,z147,z4,z8,z6]),(1,[z1,z148,z3,z4,z8,z6]),(0,[z1,z149,z87,z3,z4,z8,z6]),(0,[z1,z2,z150,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z60,z6])]],
   [[(0,[z17,z1,z2,z3,z4,z22,z8]),(0,[z0,z1,z2,z3,z4,z8,z151]),(0,[z18,z1,z2,z48,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z141,z6]),(0,[z152,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z153,z6]),(0,[z1,z2,z40,z3,z4,z8,z154])],[(0,[z1,z2,z3,z4,z155,z8,z6]),(0,[z84,z1,z2,z156,z4,z8,z6]),(0,[z78,z1,z2,z3,z81,z8,z6]),(0,[z1,z2,z157,z3,z4,z8,z6]),(0,[z1,z158,z2,z3,z4,z8,z6]),(0,[z1,z159,z2,z11,z3,z4,z8]),(0,[z1,z2,z3,z4,z22,z19,z8])],[(0,[z1,z2,z160,z3,z4,z8,z6]),(0,[z17,z2,z3,z63,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z161]),(0,[z1,z149,z2,z11,z3,z4,z8]),(0,[z1,z2,z162,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z163]),(0,[z1,z2,z3,z4,z8,z91,z6]),(0,[z1,z2,z3,z4,z22,z8,z164])],[(0,[z130,z84,z2,z3,z4,z8,z6]),(0,[z1,z165,z2,z3,z4,z8,z6]),(0,[z1,z26,z2,z61,z4,z8,z6]),(0,[z1,z2,z3,z4,z166,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z167]),(0,[z168,z1,z2,z3,z4,z8,z6])],[(1,[z1,z2,z3,z4,z8,z169]),(0,[z1,z2,z11,z3,z4,z8,z5]),(0,[z1,z2,z170,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z47,z171]),(0,[z1,z2,z3,z4,z8,z172,z47]),(0,[z1,z2,z3,z119,z4,z8,z121])],[(1,[z1,z144,z3,z21,z8,z6]),(0,[z1,z2,z173,z3,z4,z8,z6]),(0,[z1,z2,z174,z11,z3,z4,z8])],[(0,[z17,z1,z2,z3,z4,z64,z6]),(0,[z0,z1,z2,z3,z4,z8,z175]),(0,[z1,z2,z3,z4,z176,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z177]),(0,[z1,z2,z48,z3,z4,z19,z6]),(0,[z1,z2,z178,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z179,z6]),(0,[z1,z2,z3,z86,z4,z15,z8]),(0,[z18,z1,z3,z4,z180,z8,z6]),(0,[z1,z181,z2,z3,z4,z8,z6]),(0,[z1,z2,z48,z3,z4,z22,z8]),(0,[z1,z2,z3,z79,z4,z8,z172])]],
   [[(0,[z182,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z183,z8,z6]),(0,[z1,z2,z3,z184,z4,z8,z6]),(0,[z1,z2,z3,z4,z185,z8,z6]),(0,[z1,z2,z3,z4,z22,z64,z8]),(0,[z18,z1,z2,z3,z186,z8,z6]),(0,[z187,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z188,z6]),(1,[z1,z2,z106,z4,z8,z16]),(0,[z1,z2,z3,z7,z4,z8,z16])],[(1,[z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z189,z8,z6]),(0,[z1,z2,z11,z3,z4,z8,z16])],[(0,[z1,z2,z3,z147,z4,z8,z6]),(0,[z1,z2,z3,z21,z4,z8,z47]),(0,[z1,z2,z11,z3,z4,z8,z8])],[(0,[z1,z190,z2,z3,z4,z8,z6]),(0,[z1,z2,z11,z3,z147,z4,z8]),(0,[z18,z1,z2,z11,z3,z4,z8]),(0,[z1,z2,z3,z79,z4,z22,z8])],[(0,[z191,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z192,z6]),(0,[z1,z2,z3,z4,z8,z193,z6]),(0,[z1,z2,z3,z4,z22,z8,z108])],[(0,[z194,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z195,z8,z47]),(0,[z1,z2,z9,z3,z4,z8,z6]),(0,[z1,z2,z41,z3,z4,z8,z12]),(0,[z1,z2,z196,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z197,z8,z6])],[(1,[z84,z127,z3,z4,z8,z6]),(0,[z78,z138,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z97,z4,z6]),(0,[z1,z2,z3,z198,z4,z8,z6]),(0,[z38,z1,z2,z3,z4,z8,z47]),(0,[z199,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z200,z47]),(0,[z1,z2,z41,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z201,z22,z8])],[(0,[z202,z1,z2,z3,z4,z8,z6]),(0,[z78,z1,z2,z3,z4,z22,z8]),(0,[z0,z1,z2,z3,z119,z4,z6]),(1,[z1,z2,z3,z4,z203,z6]),(0,[z1,z2,z204,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z205,z8,z6]),(0,[z1,z2,z3,z4,z8,z206,z6]),(0,[z1,z2,z3,z4,z207,z8,z6]),(0,[z1,z2,z208,z3,z4,z8,z6]),(0,[z1,z118,z2,z3,z4,z91,z6]),(0,[z1,z2,z209,z3,z4,z8,z6]),(0,[z1,z2,z210,z3,z4,z8,z6]),(1,[z2,z3,z4,z8,z211,z6]),(0,[z1,z2,z11,z3,z212,z4,z8])],[(0,[z84,z1,z127,z3,z4,z8,z6]),(0,[z1,z2,z213,z3,z4,z8,z6]),(0,[z1,z2,z3,z214,z4,z8,z6]),(0,[z215,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z47,z216]),(0,[z1,z2,z3,z79,z8,z172,z6])],[(0,[z217,z1,z2,z11,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z46,z6]),(0,[z1,z2,z218,z3,z4,z8,z6]),(0,[z1,z219,z3,z4,z8,z108,z6]),(0,[z220,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z221,z6]),(0,[z1,z2,z222,z3,z4,z8,z6]),(0,[z223,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z224,z3,z4,z8,z6]),(0,[z1,z118,z2,z11,z3,z4,z6]),(0,[z2,z3,z4,z8,z211,z46,z6])],[(0,[z1,z2,z3,z4,z8,z6,z225]),(1,[z1,z2,z3,z4,z8,z226]),(0,[z78,z2,z3,z4,z15,z8,z6]),(0,[z1,z2,z43,z3,z4,z15,z6]),(0,[z1,z2,z3,z4,z227,z8,z6]),(0,[z1,z2,z3,z4,z8,z228,z6]),(0,[z1,z2,z3,z4,z22,z91,z6])],[(0,[z1,z2,z83,z11,z3,z4,z8]),(0,[z229,z1,z2,z3,z4,z8,z6]),(0,[z1,z26,z2,z4,z19,z8,z6]),(0,[z71,z1,z2,z3,z4,z8,z16]),(0,[z1,z230,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z231,z4,z8,z6]),(0,[z1,z149,z2,z3,z4,z60,z6]),(0,[z1,z2,z232,z3,z4,z8,z6]),(0,[z1,z2,z3,z79,z4,z8,z93])],[(0,[z1,z2,z3,z4,z8,z233,z6]),(0,[z1,z2,z3,z4,z8,z16,z234]),(0,[z235,z1,z2,z3,z4,z22,z8])]],
   [[(0,[z1,z2,z236,z3,z4,z8,z6]),(0,[z237,z1,z2,z3,z4,z8,z6]),(0,[z18,z1,z2,z3,z4,z111,z6]),(0,[z1,z118,z2,z3,z4,z22,z8]),(0,[z1,z2,z3,z4,z180,z8,z47]),(0,[z1,z2,z238,z3,z4,z8,z6]),(0,[z1,z2,z239,z3,z4,z8,z46]),(0,[z1,z2,z240,z3,z4,z8,z6])],[(0,[z241,z1,z2,z3,z4,z8,z6]),(0,[z217,z84,z2,z3,z4,z8,z6]),(0,[z1,z2,z242,z3,z4,z8,z6]),(0,[z1,z2,z87,z3,z4,z8,z47]),(0,[z1,z59,z2,z3,z4,z8,z47]),(0,[z1,z149,z2,z3,z4,z91,z6]),(1,[z1,z2,z29,z3,z4,z8]),(0,[z1,z2,z3,z243,z4,z8,z6]),(0,[z1,z2,z41,z3,z4,z8,z70]),(0,[z1,z2,z3,z4,z8,z70,z6])],[(0,[z1,z2,z3,z4,z8,z244,z6]),(0,[z245,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z246,z6])],[(0,[z130,z1,z2,z3,z4,z22,z8]),(0,[z1,z2,z58,z3,z4,z8,z6]),(0,[z17,z1,z2,z247,z4,z8,z6]),(0,[z1,z2,z3,z4,z248,z8,z6]),(0,[z1,z26,z2,z3,z4,z22,z8]),(0,[z1,z2,z249,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z250,z6])],[(0,[z217,z251,z2,z3,z4,z8,z6]),(0,[z1,z2,z85,z4,z99,z8,z6]),(0,[z1,z2,z3,z252,z4,z8,z6]),(0,[z253,z1,z2,z3,z4,z22,z8]),(0,[z1,z2,z3,z4,z22,z22,z8])],[(0,[z1,z2,z3,z4,z8,z254,z6]),(1,[z1,z2,z4,z8,z255,z6]),(0,[z1,z256,z2,z3,z4,z8,z6]),(0,[z1,z2,z11,z3,z4,z197,z8])],[(0,[z130,z1,z2,z3,z4,z8,z257]),(0,[z1,z258,z2,z3,z4,z8,z6]),(0,[z1,z2,z11,z3,z4,z99,z8]),(0,[z1,z2,z3,z4,z8,z259,z6]),(0,[z1,z260,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z261,z6]),(0,[z1,z2,z3,z4,z8,z105,z16])]],
   [[(0,[z1,z2,z147,z4,z8,z108,z6]),(0,[z1,z2,z11,z3,z4,z180,z8]),(0,[z1,z159,z2,z3,z4,z22,z8]),(0,[z1,z2,z11,z3,z4,z8,z108]),(0,[z1,z2,z262,z11,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z6,z263])],[(0,[z1,z264,z2,z3,z4,z8,z6]),(0,[z1,z149,z2,z3,z4,z22,z8]),(0,[z1,z2,z265,z3,z4,z8,z6])],[(0,[z1,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z75,z93]),(1,[z1,z2,z3,z4,z8,z266])],[(0,[z1,z2,z3,z4,z267,z8,z6]),(0,[z1,z2,z3,z4,z268,z8,z6]),(0,[z1,z127,z2,z3,z4,z8,z47]),(1,[z1,z2,z106,z4,z8,z6]),(0,[z1,z2,z3,z4,z19,z8,z47]),(0,[z1,z2,z3,z4,z8,z6,z171]),(0,[z1,z2,z3,z4,z8,z269,z6]),(0,[z1,z2,z3,z4,z8,z6,z270]),(0,[z1,z2,z55,z3,z4,z271,z6])],[(0,[z1,z2,z272,z3,z4,z8,z6]),(0,[z18,z1,z3,z27,z4,z8,z6]),(0,[z1,z2,z3,z4,z273,z8,z6])],[(0,[z1,z2,z3,z4,z8,z274,z6]),(0,[z1,z59,z3,z4,z275,z8,z6]),(0,[z1,z276,z2,z3,z4,z8,z6]),(0,[z1,z2,z11,z277,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z278,z6])],[(0,[z251,z1,z2,z11,z3,z4,z8]),(0,[z74,z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z279,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z280]),(1,[z1,z3,z4,z8,z193,z6])],[(0,[z78,z1,z2,z3,z63,z8,z6]),(0,[z78,z1,z2,z3,z4,z8,z206]),(1,[z1,z149,z2,z11,z3,z4]),(0,[z1,z2,z3,z4,z8,z60,z16]),(0,[z1,z2,z3,z4,z281,z8,z6]),(0,[z282,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z22,z8,z93])]],
   [[(0,[z1,z2,z283,z3,z4,z8,z6]),(0,[z17,z1,z2,z3,z4,z8,z47]),(0,[z1,z2,z3,z4,z8,z47,z75]),(0,[z18,z1,z2,z10,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z284]),(1,[z1,z2,z61,z99,z8,z6]),(0,[z1,z2,z285,z3,z4,z8,z108]),(1,[z1,z2,z3,z4,z271,z6])],[(0,[z1,z2,z3,z4,z8,z286,z6]),(0,[z38,z1,z2,z41,z3,z4,z8]),(0,[z1,z144,z2,z11,z3,z4,z8]),(1,[z1,z2,z287,z3,z4,z6]),(1,[z288,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z211,z6]),(0,[z1,z289,z2,z3,z4,z8,z6])],[(0,[z290,z1,z2,z3,z4,z8,z6]),(0,[z18,z1,z2,z3,z4,z22,z8]),(0,[z1,z2,z3,z4,z8,z91,z16]),(0,[z1,z2,z291,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z292]),(0,[z1,z293,z2,z3,z4,z22,z8])],[(0,[z1,z83,z3,z4,z275,z8,z6]),(0,[z2,z3,z63,z4,z15,z8,z6]),(1,[z1,z2,z3,z4,z8,z175]),(0,[z18,z223,z2,z3,z4,z8,z6]),(0,[z1,z2,z294,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z22,z295,z8])],[(0,[z1,z2,z3,z4,z296,z8,z6]),(1,[z0,z2,z3,z4,z64,z6]),(0,[z1,z2,z3,z4,z297,z8,z6]),(0,[z1,z2,z3,z4,z99,z22,z8]),(0,[z1,z2,z298,z3,z4,z8,z6])],[(0,[z1,z118,z149,z3,z4,z8,z6]),(1,[z1,z2,z11,z3,z4,z216]),(0,[z1,z2,z3,z4,z8,z6,z299])],[(0,[z1,z2,z3,z4,z8,z6,z257]),(0,[z1,z2,z3,z10,z4,z8,z300]),(0,[z1,z2,z3,z4,z8,z46,z6])],[(0,[z1,z127,z3,z4,z275,z8,z6]),(0,[z1,z2,z48,z3,z4,z8,z47]),(0,[z1,z2,z40,z3,z4,z22,z8]),(0,[z1,z2,z11,z3,z4,z19,z6]),(0,[z1,z2,z11,z55,z3,z4,z8])]],
   [[(0,[z1,z2,z29,z3,z4,z8,z60]),(0,[z1,z2,z3,z4,z8,z108,z47]),(0,[z1,z2,z3,z4,z8,z6,z216])],[(0,[z1,z127,z2,z3,z4,z8,z226]),(0,[z217,z1,z2,z3,z4,z22,z8]),(1,[z1,z2,z301,z3,z4,z8]),(1,[z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z302,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z303]),(0,[z1,z2,z304,z3,z4,z22,z8])],[(0,[z1,z2,z3,z147,z4,z8,z16]),(0,[z1,z2,z305,z3,z4,z8,z6]),(0,[z1,z2,z88,z3,z8,z6,z93])],[(0,[z78,z1,z2,z3,z4,z52,z6]),(0,[z0,z1,z2,z3,z4,z22,z8]),(0,[z1,z2,z3,z4,z8,z306,z6]),(0,[z1,z2,z3,z79,z4,z8,z47])],[(1,[z1,z2,z184,z4,z8,z6]),(0,[z1,z2,z307,z3,z4,z8,z6]),(0,[z1,z2,z11,z3,z4,z8,z128]),(0,[z1,z2,z3,z4,z8,z255,z6]),(0,[z1,z2,z3,z4,z8,z47,z47])],[(0,[z1,z2,z3,z4,z8,z8,z6]),(0,[z1,z2,z218,z3,z4,z8,z5]),(0,[z1,z2,z3,z4,z308,z8,z6]),(0,[z1,z2,z9,z3,z4,z8,z16]),(0,[z1,z2,z309,z3,z4,z8,z6]),(0,[z1,z2,z11,z3,z119,z4,z8])],[(0,[z310,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z311,z6]),(0,[z1,z2,z80,z3,z4,z8,z6]),(0,[z1,z2,z3,z312,z4,z8,z6]),(0,[z199,z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z41,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z47,z12]),(0,[z313,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z81,z8,z6]),(1,[z1,z2,z3,z79,z8,z172])],[(0,[z314,z1,z2,z3,z4,z8,z6]),(0,[z78,z1,z2,z3,z4,z8,z47]),(0,[z78,z1,z2,z315,z3,z8,z6]),(0,[z1,z2,z11,z3,z4,z15,z8]),(1,[z1,z2,z4,z316,z8,z6]),(0,[z1,z2,z3,z4,z8,z47,z6]),(1,[z1,z2,z3,z4,z203,z16]),(0,[z1,z2,z317,z3,z4,z8,z6]),(0,[z318,z1,z2,z3,z4,z8,z47]),(0,[z1,z2,z9,z3,z10,z8,z6])]],
   [[(0,[z130,z1,z2,z3,z4,z8,z319]),(1,[z1,z2,z51,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z320]),(1,[z1,z2,z3,z4,z8,z321]),(0,[z1,z2,z3,z27,z4,z8,z6]),(0,[z1,z2,z3,z21,z99,z8,z6]),(0,[z1,z322,z2,z3,z4,z8,z6]),(0,[z1,z118,z3,z4,z180,z8,z6])],[(0,[z323,z1,z2,z3,z4,z8,z6]),(0,[z0,z1,z2,z3,z4,z64,z6]),(0,[z38,z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z324,z3,z4,z8,z6]),(0,[z325,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z326,z4,z8,z6]),(0,[z1,z2,z327,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z328]),(0,[z329,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z9,z147,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z330,z6]),(0,[z1,z2,z3,z4,z8,z6,z331]),(0,[z1,z2,z3,z4,z8,z332,z6]),(0,[z1,z2,z333,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z334])],[(0,[z1,z2,z3,z4,z335,z8,z6]),(0,[z0,z2,z3,z4,z64,z8,z6]),(0,[z1,z2,z3,z4,z8,z172,z75]),(0,[z1,z2,z3,z10,z21,z8,z6]),(0,[z1,z2,z3,z4,z8,z203,z6]),(0,[z1,z2,z336,z3,z4,z8,z6])],[(0,[z130,z1,z83,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z337]),(0,[z84,z1,z2,z11,z3,z4,z8]),(0,[z1,z2,z3,z4,z338,z8,z6]),(0,[z138,z1,z2,z3,z63,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z339]),(0,[z1,z2,z3,z4,z8,z340,z6]),(0,[z1,z26,z87,z3,z4,z8,z6])],[(0,[z341,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z342,z4,z8,z6]),(0,[z1,z2,z343,z3,z4,z8,z6]),(0,[z1,z2,z344,z3,z4,z8,z6]),(0,[z98,z1,z2,z3,z4,z8,z6])],[(0,[z345,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z346,z3,z4,z8,z6]),(0,[z18,z1,z149,z3,z4,z8,z6]),(1,[z1,z26,z87,z4,z8,z6]),(0,[z1,z26,z2,z11,z3,z4,z8]),(0,[z1,z149,z2,z3,z4,z8,z177]),(0,[z1,z2,z3,z347,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z8,z6,z348]),(0,[z1,z2,z349,z3,z4,z8,z6]),(0,[z1,z118,z2,z3,z4,z8,z47]),(0,[z1,z2,z3,z4,z350,z8,z6]),(0,[z1,z2,z351,z11,z3,z4,z8])],[(1,[z1,z2,z156,z4,z8,z6]),(0,[z1,z2,z116,z3,z8,z5,z6]),(0,[z1,z2,z3,z352,z4,z8,z6]),(0,[z1,z144,z2,z3,z21,z8,z6]),(0,[z1,z2,z3,z4,z8,z353,z6]),(0,[z1,z2,z354,z3,z4,z8,z6])],[(0,[z1,z2,z3,z355,z4,z8,z6]),(0,[z1,z2,z301,z3,z4,z180,z8]),(0,[z1,z2,z3,z134,z4,z8,z6]),(0,[z1,z2,z3,z10,z4,z22,z8]),(0,[z1,z2,z48,z40,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z356]),(0,[z1,z2,z3,z81,z8,z46,z6])],[(0,[z130,z1,z2,z3,z4,z8,z47]),(0,[z1,z2,z11,z85,z3,z4,z8]),(0,[z1,z2,z357,z4,z275,z8,z6]),(0,[z1,z358,z2,z3,z4,z8,z6]),(0,[z1,z2,z249,z3,z4,z8,z16]),(0,[z1,z2,z359,z3,z4,z22,z8])],[(0,[z1,z2,z147,z4,z99,z8,z6]),(0,[z1,z360,z2,z3,z4,z8,z6]),(1,[z138,z2,z3,z63,z8,z6]),(0,[z1,z2,z3,z4,z22,z8,z47]),(0,[z1,z361,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z362,z4,z8,z6]),(0,[z1,z363,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z364,z4,z8,z6]),(0,[z365,z1,z2,z11,z3,z4,z8])],[(0,[z251,z1,z2,z3,z4,z22,z8]),(0,[z1,z2,z58,z3,z147,z4,z8]),(0,[z38,z1,z2,z3,z4,z8,z75]),(0,[z366,z1,z2,z3,z4,z8,z6]),(0,[z1,z144,z2,z3,z4,z8,z284]),(1,[z1,z2,z4,z8,z255,z16]),(0,[z1,z2,z3,z4,z8,z16,z93]),(0,[z1,z367,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z164,z6])],[(1,[z130,z83,z3,z4,z8,z6]),(0,[z368,z1,z2,z3,z4,z8,z6]),(0,[z38,z1,z2,z3,z79,z4,z8]),(0,[z369,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z370,z3,z4,z8,z6]),(0,[z1,z2,z3,z371,z4,z8,z6]),(0,[z1,z372,z2,z3,z4,z8,z6])],[(0,[z1,z373,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z275,z22,z8]),(0,[z1,z2,z3,z374,z4,z8,z6])]],
   [[(0,[z1,z375,z2,z3,z4,z8,z6]),(0,[z138,z1,z2,z11,z3,z4,z8]),(0,[z1,z2,z3,z63,z4,z22,z8]),(0,[z1,z144,z2,z3,z4,z22,z8]),(0,[z1,z159,z2,z3,z4,z8,z47]),(0,[z1,z2,z3,z4,z8,z376,z6])],[(0,[z84,z1,z2,z377,z4,z8,z6]),(0,[z1,z149,z2,z3,z4,z8,z47]),(0,[z1,z2,z378,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z379,z8,z6])],[(0,[z1,z2,z3,z4,z8,z6,z380]),(0,[z381,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z172,z6]),(0,[z1,z2,z11,z3,z4,z22,z6])],[(0,[z1,z2,z3,z4,z8,z6,z382]),(0,[z1,z2,z3,z383,z4,z8,z6]),(0,[z1,z2,z384,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z385,z8,z6]),(0,[z1,z2,z3,z386,z4,z8,z6]),(0,[z1,z2,z387,z3,z4,z8,z6]),(0,[z74,z1,z2,z55,z3,z4,z8]),(0,[z18,z1,z2,z87,z4,z8,z6]),(1,[z1,z2,z150,z4,z8,z6])],[(0,[z388,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z389,z4,z8,z6]),(0,[z1,z390,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z391,z8,z6]),(0,[z1,z2,z3,z4,z91,z6,z216])],[(0,[z1,z127,z2,z3,z4,z8,z16]),(0,[z18,z392,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z393]),(0,[z1,z2,z3,z4,z316,z8,z6]),(0,[z1,z2,z3,z4,z19,z8,z16]),(0,[z1,z2,z239,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z22,z81,z8])],[(0,[z1,z2,z394,z3,z4,z8,z6]),(1,[z1,z2,z3,z110,z8,z6]),(0,[z18,z1,z2,z3,z4,z248,z6]),(0,[z1,z2,z3,z4,z8,z6,z161]),(0,[z1,z2,z3,z4,z8,z395,z6]),(0,[z1,z2,z3,z8,z172,z6,z93])]],
   [[(0,[z1,z2,z3,z396,z4,z8,z6]),(0,[z1,z2,z3,z21,z4,z8,z6]),(0,[z1,z118,z2,z3,z4,z60,z6]),(0,[z1,z397,z2,z11,z3,z4,z8])],[(0,[z1,z2,z398,z3,z4,z8,z6]),(0,[z74,z1,z2,z3,z4,z8,z128]),(1,[z1,z2,z287,z3,z4,z16]),(0,[z1,z2,z3,z10,z4,z8,z107])],[(0,[z18,z1,z2,z3,z4,z8,z47]),(0,[z31,z1,z2,z3,z4,z8,z6]),(1,[z1,z2,z287,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z6,z399]),(1,[z1,z2,z3,z4,z8,z103])],[(0,[z1,z2,z400,z3,z4,z15,z8]),(0,[z1,z2,z401,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z402,z8,z6]),(0,[z1,z2,z3,z4,z195,z8,z6]),(0,[z1,z2,z55,z3,z4,z22,z8])],[(0,[z1,z2,z3,z4,z8,z200,z6]),(0,[z1,z2,z3,z403,z4,z8,z6]),(0,[z38,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z404,z8,z6]),(0,[z1,z2,z3,z4,z99,z8,z47]),(0,[z1,z2,z61,z3,z4,z22,z8]),(0,[z1,z2,z3,z4,z22,z8,z46]),(0,[z1,z2,z11,z11,z3,z4,z8])],[(0,[z405,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z175,z6]),(0,[z1,z2,z3,z4,z8,z406,z6]),(0,[z1,z2,z3,z407,z4,z8,z6]),(0,[z1,z2,z408,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z409]),(0,[z1,z2,z3,z4,z8,z6,z12]),(0,[z1,z2,z3,z119,z81,z8,z6])],[(0,[z1,z2,z3,z4,z8,z410,z6]),(0,[z1,z2,z3,z4,z8,z6,z6]),(0,[z1,z2,z411,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z46,z16])],[(0,[z0,z1,z2,z11,z3,z4,z8]),(0,[z1,z26,z2,z3,z4,z8,z192]),(0,[z1,z144,z2,z3,z4,z8,z395]),(0,[z1,z2,z40,z3,z4,z8,z47]),(0,[z1,z2,z3,z4,z8,z6,z412])]],
   [[(0,[z251,z2,z3,z147,z4,z8,z6]),(0,[z1,z2,z3,z4,z413,z8,z6]),(0,[z2,z3,z4,z64,z8,z5,z6]),(0,[z1,z2,z3,z414,z4,z8,z6]),(0,[z1,z2,z11,z3,z4,z19,z8]),(1,[z1,z2,z3,z4,z8,z415])],[(1,[z1,z2,z3,z4,z8,z49]),(0,[z217,z1,z2,z3,z4,z8,z47]),(0,[z138,z1,z2,z3,z81,z8,z6]),(0,[z1,z2,z416,z3,z4,z8,z6]),(0,[z1,z2,z40,z3,z4,z8,z409])],[(0,[z417,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z418,z3,z4,z8,z6]),(0,[z1,z2,z3,z419,z4,z8,z6]),(0,[z1,z2,z420,z3,z4,z8,z6]),(0,[z421,z1,z2,z3,z4,z8,z6]),(0,[z422,z1,z2,z3,z4,z8,z6]),(0,[z1,z144,z3,z21,z4,z8,z6]),(0,[z1,z423,z2,z3,z4,z8,z6])],[(0,[z84,z1,z2,z3,z4,z22,z8]),(0,[z1,z2,z424,z3,z4,z8,z6]),(1,[z1,z2,z411,z4,z8,z6]),(0,[z1,z2,z3,z4,z22,z8,z172]),(0,[z1,z2,z425,z3,z4,z8,z6])],[(0,[z1,z2,z83,z3,z4,z8,z47]),(0,[z1,z2,z85,z3,z4,z8,z47]),(0,[z1,z26,z2,z10,z4,z8,z6]),(0,[z1,z2,z3,z426,z4,z8,z6]),(0,[z1,z2,z3,z4,z180,z108,z6]),(0,[z1,z2,z3,z4,z8,z255,z16]),(0,[z427,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z428,z6]),(0,[z1,z2,z429,z3,z4,z8,z6])],[(0,[z430,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z377,z4,z8,z6]),(0,[z1,z2,z3,z431,z4,z8,z6]),(0,[z1,z2,z309,z3,z4,z8,z16]),(0,[z1,z2,z432,z3,z4,z8,z6])],[(0,[z433,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z180,z8,z6]),(1,[z1,z2,z3,z4,z8,z188]),(0,[z1,z2,z3,z4,z81,z8,z16]),(0,[z1,z2,z11,z3,z10,z4,z8]),(0,[z1,z2,z55,z3,z4,z8,z93]),(0,[z434,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z83,z3,z4,z8,z6]),(0,[z1,z2,z85,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z435,z8,z6]),(0,[z1,z2,z11,z3,z4,z64,z8]),(0,[z1,z2,z3,z4,z8,z436,z6]),(0,[z1,z2,z87,z3,z4,z8,z6]),(0,[z1,z59,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z76]),(0,[z1,z2,z3,z4,z8,z47,z16])]],
   [[(0,[z1,z2,z3,z27,z4,z8,z16]),(0,[z1,z159,z3,z4,z8,z6,z16]),(0,[z1,z2,z3,z437,z4,z8,z6]),(0,[z1,z2,z438,z3,z4,z8,z47]),(0,[z1,z2,z439,z3,z4,z8,z6]),(0,[z71,z1,z2,z11,z3,z4,z8])],[(0,[z440,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z441,z8,z6]),(0,[z323,z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z95,z3,z4,z8,z6]),(0,[z1,z2,z315,z11,z3,z4,z8])],[(0,[z1,z59,z2,z3,z275,z8,z6]),(0,[z1,z2,z3,z442,z4,z22,z8])],[(1,[z1,z2,z3,z4,z443,z6]),(0,[z1,z2,z3,z4,z8,z203,z16]),(0,[z1,z2,z3,z4,z8,z444,z6]),(0,[z1,z2,z3,z4,z445,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z446]),(0,[z1,z2,z3,z119,z4,z8,z415]),(0,[z1,z2,z3,z119,z4,z22,z8])],[(0,[z1,z2,z3,z97,z4,z15,z6]),(0,[z1,z447,z2,z3,z4,z8,z6]),(0,[z1,z2,z287,z3,z4,z8,z6]),(0,[z1,z2,z88,z11,z3,z4,z8]),(0,[z1,z2,z3,z4,z22,z8,z216])],[(0,[z1,z2,z448,z3,z4,z8,z6]),(0,[z1,z2,z41,z55,z4,z8,z6]),(0,[z1,z2,z3,z4,z449,z22,z8])],[(0,[z1,z450,z2,z3,z4,z8,z6]),(0,[z451,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z452,z8,z6]),(0,[z1,z2,z3,z4,z8,z453,z6])],[(0,[z1,z2,z156,z3,z4,z8,z6]),(0,[z138,z1,z2,z3,z4,z22,z8]),(1,[z1,z2,z3,z207,z8,z6]),(1,[z1,z2,z40,z4,z19,z6])]],
   [[(0,[z1,z2,z3,z4,z8,z319,z6]),(0,[z1,z2,z3,z4,z8,z226,z6]),(1,[z1,z2,z3,z4,z8,z151]),(0,[z1,z454,z2,z3,z4,z8,z6]),(0,[z1,z2,z11,z3,z4,z8,z46])],[(0,[z1,z127,z2,z3,z4,z8,z6]),(0,[z1,z144,z83,z3,z4,z8,z6]),(0,[z138,z2,z3,z63,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z455,z6]),(0,[z1,z2,z3,z4,z19,z8,z6]),(0,[z456,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z457,z8,z6]),(0,[z1,z2,z458,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z459,z8,z6]),(0,[z1,z2,z3,z10,z4,z8,z47]),(0,[z1,z460,z2,z3,z4,z8,z6]),(0,[z1,z2,z315,z3,z8,z46,z6])],[(1,[z1,z398,z3,z4,z8,z6]),(1,[z1,z2,z55,z4,z8,z70])],[(0,[z1,z2,z3,z4,z8,z461,z6]),(0,[z1,z2,z3,z4,z462,z8,z6]),(1,[z1,z2,z3,z4,z195,z8]),(0,[z1,z3,z4,z8,z193,z108,z6]),(1,[z1,z2,z3,z4,z8,z154]),(0,[z463,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z11,z464,z3,z4,z8])],[(0,[z1,z2,z3,z4,z465,z8,z6]),(0,[z251,z1,z2,z3,z4,z8,z47]),(0,[z1,z87,z3,z4,z180,z8,z6]),(0,[z1,z2,z3,z4,z8,z466,z6]),(0,[z1,z2,z11,z467,z3,z4,z8]),(0,[z1,z2,z3,z4,z468,z22,z8])],[(0,[z469,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z86,z4,z8,z6]),(0,[z17,z1,z2,z3,z4,z8,z6]),(0,[z1,z470,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z471]),(0,[z1,z2,z3,z4,z8,z472,z47])],[(0,[z17,z1,z2,z458,z4,z8,z6]),(0,[z1,z2,z3,z4,z275,z8,z47]),(1,[z1,z2,z48,z4,z108,z6]),(0,[z1,z2,z11,z3,z4,z8,z172])]],
   [[(0,[z1,z473,z2,z3,z4,z8,z6]),(0,[z251,z1,z2,z3,z4,z8,z6]),(1,[z251,z2,z147,z4,z8,z6]),(0,[z1,z2,z3,z63,z4,z8,z47]),(0,[z1,z2,z3,z4,z8,z474,z6]),(0,[z1,z2,z3,z10,z275,z8,z6]),(0,[z1,z144,z2,z3,z4,z8,z47])],[(0,[z1,z2,z3,z4,z8,z5,z47]),(1,[z1,z2,z218,z3,z4,z8]),(0,[z74,z1,z2,z11,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z472,z6]),(0,[z1,z2,z3,z4,z475,z8,z6]),(0,[z1,z2,z3,z4,z8,z476,z6])],[(0,[z1,z2,z3,z4,z64,z46,z6]),(0,[z1,z2,z3,z4,z477,z8,z6]),(0,[z1,z2,z3,z4,z8,z172,z16]),(0,[z1,z2,z3,z4,z8,z478,z6]),(0,[z1,z2,z479,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z480,z6]),(0,[z1,z2,z3,z4,z8,z481,z6]),(0,[z78,z1,z148,z3,z4,z8,z6]),(1,[z1,z2,z247,z4,z8,z6]),(0,[z1,z2,z3,z4,z482,z8,z6]),(0,[z1,z2,z3,z4,z8,z483,z6]),(0,[z1,z2,z3,z4,z459,z8,z60]),(0,[z1,z159,z2,z3,z4,z8,z16]),(0,[z1,z2,z48,z3,z4,z108,z6]),(0,[z1,z2,z484,z3,z4,z8,z6]),(0,[z1,z2,z11,z3,z4,z22,z8]),(0,[z1,z2,z3,z4,z295,z8,z6])],[(0,[z1,z2,z3,z4,z8,z5,z6]),(0,[z38,z2,z3,z4,z8,z75,z6])],[(0,[z485,z1,z2,z3,z4,z8,z6]),(0,[z486,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z81,z5,z6]),(0,[z1,z3,z4,z180,z8,z60,z6]),(0,[z1,z2,z3,z4,z8,z47,z487]),(0,[z1,z2,z48,z3,z4,z8,z6])],[(0,[z488,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z64,z8,z47]),(0,[z2,z3,z4,z8,z75,z6,z128]),(0,[z18,z1,z2,z41,z4,z8,z6]),(0,[z1,z144,z2,z3,z275,z8,z6]),(0,[z1,z2,z3,z4,z8,z108,z6]),(0,[z1,z2,z489,z3,z4,z8,z6]),(0,[z1,z2,z301,z11,z3,z4,z8])],[(0,[z1,z2,z3,z4,z8,z154,z6])]],
   [[(0,[z1,z2,z9,z85,z4,z8,z6]),(0,[z78,z1,z2,z3,z4,z8,z169]),(0,[z1,z59,z2,z3,z4,z8,z266]),(0,[z1,z2,z3,z21,z4,z8,z16]),(0,[z1,z2,z411,z4,z8,z60,z6]),(0,[z199,z1,z159,z3,z4,z8,z6]),(0,[z1,z2,z61,z11,z3,z4,z8]),(0,[z1,z2,z490,z3,z4,z8,z6]),(0,[z1,z2,z3,z491,z4,z8,z6])],[(0,[z1,z2,z3,z4,z64,z8,z6]),(0,[z1,z2,z3,z4,z8,z492,z6]),(1,[z1,z2,z3,z186,z8,z6]),(0,[z1,z2,z3,z79,z4,z8,z6])],[(0,[z1,z2,z11,z3,z27,z4,z8]),(1,[z1,z149,z3,z4,z60,z6]),(2,[z1,z2,z287,z3,z4]),(0,[z1,z2,z467,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z22,z8,z75]),(0,[z1,z2,z3,z4,z203,z6,z16])],[(0,[z84,z1,z83,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z493,z6]),(0,[z1,z494,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z201,z8,z6]),(1,[z1,z2,z11,z3,z4,z8])],[(0,[z318,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z495,z3,z4,z8,z6]),(0,[z78,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z496,z6]),(0,[z1,z2,z497,z3,z4,z8,z6])],[(1,[z17,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z498,z8,z6]),(0,[z499,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z16]),(0,[z1,z2,z11,z3,z4,z8,z93])],[(0,[z1,z2,z116,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z19,z180,z6]),(0,[z1,z2,z61,z4,z99,z8,z6]),(0,[z1,z2,z88,z3,z4,z8,z172]),(0,[z71,z1,z2,z3,z4,z22,z8])]],
   [[(0,[z1,z2,z500,z3,z4,z8,z6]),(0,[z1,z26,z2,z87,z4,z8,z6]),(0,[z1,z501,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z502,z6]),(0,[z1,z2,z3,z4,z8,z6,z503]),(0,[z1,z2,z315,z3,z4,z22,z8]),(0,[z1,z2,z3,z4,z8,z504,z6])],[(0,[z1,z2,z505,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z321,z6]),(0,[z1,z2,z3,z4,z8,z266,z6]),(1,[z1,z2,z3,z4,z8,z145]),(0,[z199,z1,z2,z11,z3,z4,z8])],[(0,[z1,z506,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z507,z6]),(1,[z1,z2,z400,z3,z4,z8]),(0,[z1,z2,z3,z4,z508,z8,z6]),(0,[z1,z26,z2,z3,z4,z8,z161]),(1,[z1,z2,z3,z4,z201,z8]),(0,[z1,z2,z40,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z16,z216]),(0,[z1,z2,z3,z4,z8,z153,z108])],[(0,[z84,z1,z2,z3,z4,z8,z47]),(0,[z1,z2,z509,z3,z4,z8,z6]),(1,[z78,z2,z3,z15,z8,z6]),(0,[z1,z2,z3,z4,z510,z8,z6]),(0,[z1,z2,z3,z4,z8,z511,z6]),(0,[z1,z2,z88,z3,z4,z22,z8])],[(0,[z1,z512,z2,z3,z4,z8,z6]),(0,[z78,z1,z2,z3,z15,z8,z6]),(0,[z1,z2,z3,z4,z513,z8,z6]),(0,[z1,z514,z2,z3,z4,z8,z6]),(0,[z515,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z516,z4,z8,z6]),(0,[z1,z2,z517,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z75,z6]),(0,[z74,z2,z3,z4,z8,z6,z128]),(0,[z1,z2,z3,z4,z8,z6,z320]),(0,[z1,z2,z3,z4,z8,z471,z6]),(0,[z235,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z518,z8,z6]),(0,[z1,z2,z3,z4,z8,z519,z6]),(0,[z1,z26,z2,z3,z4,z8,z47]),(0,[z1,z118,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z180,z8,z16]),(0,[z1,z2,z41,z4,z8,z6,z12]),(0,[z1,z2,z3,z4,z520,z8,z6])],[(0,[z1,z2,z83,z3,z4,z8,z16]),(0,[z1,z2,z40,z147,z4,z8,z6]),(0,[z1,z2,z3,z521,z4,z8,z6]),(0,[z1,z2,z85,z3,z4,z8,z16]),(0,[z1,z2,z87,z3,z4,z8,z16]),(0,[z1,z59,z2,z3,z4,z8,z16]),(1,[z1,z2,z3,z4,z8,z300])]],
   [[(1,[z38,z2,z3,z4,z8,z75])],[(0,[z130,z1,z2,z3,z4,z8,z6]),(1,[z1,z2,z377,z4,z8,z6]),(0,[z1,z522,z2,z3,z4,z8,z6]),(0,[z1,z26,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z111,z6]),(0,[z1,z2,z523,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z524,z47]),(0,[z1,z2,z3,z4,z22,z8,z12]),(0,[z1,z2,z315,z3,z4,z81,z6]),(0,[z1,z2,z3,z4,z8,z6,z121])],[(0,[z1,z2,z3,z525,z4,z8,z6]),(0,[z1,z2,z3,z247,z4,z8,z6]),(0,[z253,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z47,z128]),(0,[z1,z87,z3,z27,z4,z8,z6]),(0,[z1,z526,z2,z3,z4,z8,z6]),(0,[z1,z2,z4,z316,z8,z60,z6]),(0,[z1,z2,z351,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z22,z8,z6])],[(0,[z1,z2,z3,z4,z527,z8,z6]),(0,[z1,z2,z3,z528,z4,z8,z6]),(0,[z529,z1,z2,z3,z4,z8,z6]),(0,[z1,z530,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z119,z4,z8,z47]),(0,[z1,z219,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z531,z6]),(0,[z1,z2,z3,z4,z532,z8,z6]),(0,[z1,z2,z3,z4,z8,z524,z6]),(0,[z1,z2,z287,z3,z4,z8,z16])],[(0,[z288,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z533,z6])],[(0,[z1,z2,z3,z4,z15,z22,z8]),(0,[z1,z534,z2,z3,z4,z8,z6]),(0,[z1,z159,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z16,z337]),(0,[z1,z2,z88,z3,z4,z8,z93])],[(0,[z138,z1,z2,z3,z4,z8,z47]),(0,[z138,z1,z2,z315,z3,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z535]),(0,[z536,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z537,z8,z6]),(0,[z1,z149,z2,z3,z4,z8,z6]),(0,[z538,z1,z2,z3,z4,z8,z47])]],
   [[(0,[z1,z2,z3,z4,z8,z539,z6]),(0,[z74,z1,z2,z3,z4,z22,z8]),(0,[z1,z2,z88,z3,z79,z8,z6])],[(0,[z540,z1,z2,z3,z4,z8,z6]),(0,[z1,z541,z2,z3,z4,z8,z6]),(0,[z18,z1,z2,z4,z8,z70,z6]),(0,[z542,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z543,z3,z4,z8,z6]),(1,[z1,z219,z3,z4,z8,z6])],[(0,[z1,z2,z544,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z545,z6]),(0,[z1,z2,z546,z3,z4,z8,z6]),(0,[z1,z2,z55,z3,z4,z8,z172]),(0,[z1,z2,z174,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z6,z547]),(0,[z1,z548,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z22,z8,z60]),(0,[z1,z2,z3,z549,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z6,z550]),(0,[z1,z2,z3,z4,z8,z6,z169]),(1,[z1,z2,z3,z4,z8,z192]),(0,[z1,z2,z150,z4,z275,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z487]),(0,[z1,z2,z3,z4,z551,z8,z6]),(0,[z1,z2,z3,z4,z22,z8,z504])],[(0,[z17,z1,z2,z315,z3,z4,z6]),(0,[z1,z2,z3,z4,z8,z6,z552]),(0,[z1,z2,z3,z4,z8,z47,z129]),(0,[z1,z2,z553,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z22,z8,z70]),(1,[z1,z2,z467,z3,z4,z8])],[(0,[z17,z1,z2,z3,z4,z8,z16]),(1,[z1,z2,z3,z4,z554,z8]),(0,[z1,z3,z4,z8,z47,z6,z16]),(1,[z199,z1,z3,z4,z8,z47]),(0,[z1,z2,z555,z3,z4,z8,z47])],[(0,[z1,z2,z3,z556,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z271,z6]),(0,[z1,z2,z3,z557,z4,z8,z6]),(0,[z1,z2,z3,z558,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z559])]],
   [[(0,[z1,z560,z2,z3,z4,z8,z6]),(0,[z251,z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z561,z4,z8,z6]),(0,[z1,z2,z562,z3,z4,z8,z6]),(0,[z18,z1,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z284]),(0,[z1,z2,z106,z4,z8,z6,z16]),(0,[z1,z293,z2,z3,z4,z8,z6])],[(0,[z17,z1,z2,z3,z119,z4,z6]),(0,[z563,z1,z2,z3,z4,z8,z6]),(0,[z199,z1,z3,z4,z8,z47,z6]),(0,[z1,z2,z555,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z564]),(0,[z288,z2,z3,z4,z8,z46,z6]),(0,[z565,z1,z2,z3,z4,z8,z6]),(0,[z1,z566,z2,z3,z4,z8,z6])],[(0,[z567,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z568,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z99,z8,z6]),(0,[z569,z1,z2,z3,z4,z8,z6]),(0,[z570,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z571,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z572,z8,z6]),(1,[z1,z159,z3,z4,z8,z16]),(0,[z1,z2,z11,z3,z4,z8,z47]),(0,[z1,z2,z40,z3,z4,z108,z6]),(1,[z1,z2,z3,z4,z22,z8]),(0,[z573,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z147,z4,z22,z8]),(0,[z1,z2,z3,z4,z8,z5,z16]),(1,[z223,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z275,z99,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z574]),(0,[z575,z1,z2,z3,z4,z8,z6])],[(0,[z251,z1,z2,z147,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z172,z128]),(0,[z1,z2,z3,z4,z8,z6,z576]),(0,[z1,z2,z48,z3,z4,z8,z16]),(0,[z1,z2,z40,z3,z4,z8,z6])],[(1,[z1,z2,z3,z4,z8,z257]),(0,[z1,z2,z3,z4,z577,z8,z6]),(0,[z0,z1,z2,z3,z4,z8,z47]),(1,[z1,z59,z3,z275,z8,z6]),(0,[z1,z2,z3,z4,z8,z108,z16]),(0,[z1,z2,z3,z4,z8,z578,z6]),(1,[z1,z2,z11,z3,z4,z19])],[(0,[z217,z1,z2,z3,z4,z8,z6]),(0,[z1,z149,z3,z4,z8,z60,z6]),(0,[z1,z2,z9,z3,z4,z22,z8]),(0,[z1,z2,z304,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z8,z16,z393]),(0,[z199,z1,z2,z3,z4,z22,z8]),(0,[z1,z2,z41,z3,z4,z22,z8]),(0,[z1,z2,z3,z579,z4,z8,z6])],[(0,[z1,z2,z580,z3,z4,z8,z6]),(0,[z0,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z64,z8,z16]),(0,[z581,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z79,z4,z8,z16])],[(0,[z38,z1,z2,z55,z3,z4,z8]),(0,[z1,z2,z3,z4,z582,z8,z6]),(0,[z1,z2,z583,z3,z4,z8,z6]),(0,[z1,z584,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z22,z91])],[(0,[z1,z2,z585,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z586,z6])],[(0,[z1,z2,z11,z3,z4,z275,z8]),(0,[z1,z2,z3,z4,z201,z8,z16]),(0,[z1,z2,z587,z3,z4,z8,z6]),(0,[z1,z2,z315,z3,z4,z46,z6])],[(0,[z78,z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z554,z8,z6]),(0,[z1,z149,z2,z3,z4,z180,z6]),(1,[z1,z2,z3,z119,z81,z6]),(0,[z1,z2,z11,z3,z4,z81,z8])],[(0,[z1,z2,z588,z3,z4,z8,z6]),(0,[z589,z1,z2,z3,z4,z8,z6]),(0,[z74,z1,z2,z88,z3,z4,z8]),(0,[z1,z2,z590,z3,z4,z8,z6]),(0,[z1,z2,z3,z357,z4,z8,z6]),(0,[z1,z2,z438,z3,z4,z8,z6]),(0,[z1,z2,z285,z3,z4,z8,z6])],[(0,[z1,z591,z2,z3,z4,z8,z6]),(0,[z38,z1,z2,z3,z4,z8,z128]),(0,[z1,z2,z3,z4,z8,z16,z12]),(0,[z71,z1,z2,z3,z4,z8,z47])]],
   [[(0,[z78,z1,z2,z184,z4,z8,z6]),(0,[z1,z2,z3,z4,z592,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z124]),(0,[z1,z2,z315,z3,z4,z8,z47]),(0,[z1,z2,z4,z19,z8,z108,z6]),(0,[z1,z2,z3,z4,z8,z593,z6])],[(0,[z594,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z128]),(0,[z595,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z2,z3,z4,z8,z47]),(0,[z1,z2,z3,z4,z8,z47,z596])],[(0,[z1,z26,z2,z41,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z395]),(0,[z1,z2,z61,z3,z99,z8,z6]),(1,[z1,z2,z3,z4,z8,z107]),(0,[z1,z2,z3,z597,z4,z8,z6])],[(0,[z1,z2,z3,z207,z8,z5,z6]),(0,[z1,z2,z3,z4,z8,z598,z6]),(0,[z1,z2,z88,z3,z4,z8,z47]),(0,[z1,z2,z599,z3,z4,z8,z6]),(0,[z1,z2,z41,z3,z4,z8,z93]),(0,[z1,z2,z3,z4,z8,z6,z600]),(0,[z1,z2,z315,z3,z4,z8,z6]),(0,[z1,z322,z2,z11,z3,z4,z8])],[(0,[z1,z2,z2,z3,z4,z8,z6]),(0,[z78,z1,z2,z51,z4,z8,z6]),(0,[z1,z2,z3,z4,z601,z8,z6]),(0,[z1,z2,z315,z3,z119,z8,z6]),(0,[z1,z2,z3,z4,z8,z602,z6]),(1,[z1,z2,z11,z3,z4,z22])],[(0,[z17,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z22,z8,z5]),(0,[z1,z2,z262,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z75,z16]),(0,[z1,z2,z3,z603,z4,z8,z6]),(0,[z1,z2,z287,z3,z4,z6,z16])],[(0,[z1,z2,z3,z4,z8,z6,z604]),(0,[z1,z2,z3,z4,z8,z6,z605]),(0,[z606,z1,z2,z3,z4,z8,z6]),(0,[z1,z118,z2,z3,z4,z8,z16])],[(0,[z1,z2,z3,z119,z4,z81,z6])]],
   [[(0,[z1,z607,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z10,z4,z8,z6]),(0,[z1,z608,z2,z3,z4,z8,z6])],[(0,[z130,z1,z2,z3,z4,z8,z16]),(0,[z84,z2,z3,z147,z4,z8,z6]),(0,[z1,z2,z609,z3,z4,z8,z6]),(0,[z1,z610,z2,z3,z4,z8,z6]),(0,[z1,z2,z611,z3,z4,z8,z6]),(0,[z1,z26,z2,z3,z4,z8,z16]),(0,[z1,z149,z2,z3,z4,z8,z471]),(0,[z1,z2,z3,z4,z8,z612,z6]),(0,[z1,z613,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z108,z91,z6]),(0,[z1,z614,z2,z3,z4,z8,z6]),(0,[z615,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z94,z8,z6]),(0,[z1,z2,z359,z3,z4,z8,z6])],[(0,[z1,z2,z3,z616,z4,z8,z6]),(0,[z1,z2,z3,z4,z4,z8,z6]),(0,[z1,z2,z3,z617,z4,z8,z6]),(0,[z618,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z22,z8,z16])],[(0,[z619,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z620,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z206]),(0,[z78,z17,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z621,z6]),(0,[z1,z2,z3,z4,z8,z622,z6]),(0,[z1,z2,z3,z30,z4,z8,z6]),(0,[z1,z2,z3,z4,z22,z8,z8])],[(0,[z1,z2,z623,z3,z4,z8,z6]),(0,[z1,z2,z354,z11,z3,z4,z8])],[(0,[z624,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z151]),(0,[z1,z2,z3,z186,z4,z8,z6]),(0,[z1,z2,z3,z4,z275,z8,z6]),(0,[z1,z2,z3,z4,z8,z625,z6]),(0,[z1,z2,z3,z4,z8,z415,z6])],[(0,[z1,z2,z3,z626,z4,z8,z6]),(0,[z1,z2,z3,z4,z627,z8,z6]),(0,[z1,z26,z2,z147,z4,z8,z6]),(0,[z628,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z629,z3,z4,z8,z6]),(0,[z1,z2,z3,z63,z4,z8,z6]),(0,[z1,z2,z3,z4,z15,z8,z47]),(0,[z1,z144,z2,z3,z4,z8,z6]),(1,[z1,z2,z239,z3,z4,z8])],[(0,[z630,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z631,z3,z4,z8,z6]),(0,[z1,z149,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z22,z94,z8])]],
   [[(1,[z1,z2,z3,z4,z8,z319]),(0,[z1,z2,z3,z632,z4,z8,z6]),(0,[z633,z1,z2,z3,z4,z8,z6]),(1,[z217,z2,z85,z4,z8,z6]),(0,[z74,z1,z2,z3,z4,z8,z47]),(0,[z1,z2,z3,z212,z4,z8,z6])],[(0,[z1,z127,z2,z3,z4,z8,z49]),(0,[z1,z2,z3,z4,z15,z8,z6]),(1,[z1,z2,z3,z4,z8,z177]),(0,[z1,z2,z3,z4,z8,z60,z47]),(1,[z1,z2,z285,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z6,z634])],[(0,[z1,z2,z400,z3,z4,z8,z6]),(0,[z1,z2,z3,z635,z4,z8,z6]),(0,[z1,z2,z636,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z22,z8,z91])],[(1,[z1,z2,z580,z3,z4,z8]),(0,[z1,z2,z3,z4,z637,z8,z6]),(0,[z1,z2,z3,z4,z201,z180,z8]),(0,[z1,z2,z11,z3,z4,z8,z216])],[(0,[z2,z83,z3,z147,z4,z8,z6]),(0,[z1,z638,z2,z3,z4,z8,z6]),(0,[z1,z2,z639,z3,z4,z8,z6]),(1,[z1,z3,z4,z8,z47,z16]),(0,[z1,z2,z3,z4,z8,z91,z47]),(1,[z1,z2,z315,z3,z46,z6]),(0,[z1,z2,z3,z640,z4,z8,z6]),(0,[z1,z2,z378,z11,z3,z4,z8])],[(0,[z1,z2,z301,z3,z4,z8,z47])],[(0,[z1,z2,z3,z4,z8,z641,z6]),(1,[z1,z118,z3,z4,z180,z6]),(0,[z1,z2,z55,z3,z4,z8,z47])],[(1,[z1,z2,z3,z4,z52,z6]),(0,[z1,z2,z3,z642,z4,z8,z6]),(1,[z392,z2,z3,z4,z8,z6]),(0,[z1,z2,z11,z3,z21,z4,z8]),(0,[z1,z2,z61,z3,z4,z8,z47]),(0,[z1,z2,z643,z3,z4,z8,z6])]],
   [[(0,[z18,z1,z2,z85,z4,z8,z6]),(0,[z17,z2,z3,z4,z8,z5,z6]),(1,[z1,z2,z3,z4,z248,z6]),(0,[z644,z1,z2,z3,z4,z8,z6]),(0,[z18,z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z301,z3,z4,z8,z6]),(0,[z1,z2,z61,z9,z4,z8,z6]),(0,[z1,z2,z55,z3,z4,z8,z12]),(0,[z1,z2,z3,z4,z8,z103,z46]),(0,[z1,z2,z645,z3,z4,z8,z6])],[(0,[z646,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z647,z6]),(0,[z648,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z55,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z649,z6]),(0,[z1,z2,z3,z4,z99,z8,z16]),(0,[z1,z2,z61,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z650,z8,z6]),(0,[z1,z2,z3,z4,z8,z651,z6]),(0,[z652,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z653])],[(0,[z1,z2,z3,z4,z8,z654,z6]),(1,[z1,z2,z3,z4,z8,z47]),(0,[z1,z2,z3,z4,z302,z22,z8])],[(0,[z1,z2,z3,z147,z4,z8,z47]),(0,[z1,z2,z41,z11,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z655,z6])],[(0,[z18,z1,z2,z147,z4,z8,z6]),(0,[z1,z2,z40,z85,z4,z8,z6]),(0,[z656,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z657,z6]),(0,[z658,z1,z2,z3,z4,z8,z6]),(0,[z1,z26,z2,z4,z8,z70,z6]),(0,[z1,z2,z3,z4,z8,z6,z234]),(1,[z1,z2,z3,z4,z8,z409])],[(0,[z130,z2,z83,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z659])],[(0,[z217,z1,z2,z85,z4,z8,z6]),(0,[z217,z1,z2,z3,z4,z8,z16]),(0,[z1,z660,z2,z3,z4,z8,z6]),(1,[z1,z2,z458,z4,z8,z6]),(0,[z38,z1,z2,z11,z3,z4,z8]),(0,[z18,z1,z2,z3,z4,z8,z320]),(0,[z18,z1,z2,z3,z4,z8,z321]),(0,[z1,z2,z9,z3,z4,z8,z47]),(0,[z1,z2,z3,z4,z661,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z554,z8,z5]),(0,[z0,z1,z2,z315,z3,z4,z6]),(0,[z1,z662,z2,z3,z4,z8,z6]),(0,[z1,z3,z21,z4,z275,z8,z6]),(0,[z199,z1,z2,z3,z4,z8,z47]),(0,[z1,z2,z41,z3,z4,z8,z47]),(0,[z1,z2,z3,z4,z8,z6,z596]),(0,[z1,z2,z3,z4,z663,z8,z6]),(0,[z1,z664,z2,z3,z4,z8,z6])],[(0,[z84,z1,z2,z3,z4,z8,z6]),(0,[z665,z1,z2,z3,z4,z8,z6]),(0,[z0,z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z128,z93]),(0,[z1,z2,z3,z666,z4,z8,z6]),(0,[z1,z2,z3,z4,z22,z180,z8]),(0,[z1,z2,z667,z3,z4,z8,z6]),(0,[z1,z2,z464,z3,z4,z8,z6])],[(0,[z38,z74,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z27,z4,z22,z8]),(0,[z1,z2,z668,z3,z4,z8,z6]),(0,[z1,z2,z3,z119,z4,z46,z6])],[(0,[z1,z2,z580,z3,z147,z4,z8]),(0,[z1,z2,z3,z4,z8,z669,z6]),(0,[z1,z2,z48,z4,z8,z108,z6])],[(0,[z217,z1,z2,z147,z4,z8,z6]),(0,[z1,z2,z3,z4,z670,z8,z6]),(0,[z1,z2,z55,z3,z4,z8,z70])],[(0,[z84,z127,z2,z3,z4,z8,z6]),(0,[z1,z671,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z672,z6]),(0,[z1,z2,z673,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z674,z8,z6]),(0,[z1,z2,z675,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z81,z64,z6]),(0,[z1,z2,z3,z4,z8,z6,z145]),(0,[z1,z2,z11,z3,z4,z8,z91])],[(0,[z1,z676,z2,z3,z4,z8,z6]),(0,[z18,z1,z2,z61,z4,z8,z6]),(0,[z1,z2,z11,z87,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z300,z6])]],
   [[(0,[z1,z59,z144,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z677,z8,z6]),(0,[z1,z2,z3,z4,z8,z16,z16]),(0,[z1,z2,z3,z442,z4,z8,z6])],[(0,[z130,z1,z127,z3,z4,z8,z6]),(0,[z1,z148,z2,z3,z4,z8,z6]),(0,[z365,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z678,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z679,z6]),(0,[z1,z2,z3,z119,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z443,z6]),(0,[z1,z2,z680,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z681,z6]),(1,[z74,z2,z3,z4,z8,z128]),(0,[z1,z2,z11,z3,z4,z8,z75]),(0,[z1,z2,z682,z3,z4,z8,z6]),(0,[z1,z59,z2,z11,z3,z4,z8]),(1,[z1,z2,z357,z4,z8,z6])],[(1,[z1,z2,z43,z3,z4,z6]),(0,[z1,z2,z3,z4,z449,z8,z6]),(0,[z74,z1,z2,z41,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z683,z6]),(0,[z1,z2,z315,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z70,z47]),(0,[z1,z2,z11,z3,z79,z4,z8]),(0,[z1,z2,z3,z4,z8,z6,z684])],[(0,[z78,z2,z3,z4,z64,z8,z6]),(0,[z1,z2,z3,z4,z8,z685,z6]),(0,[z1,z2,z3,z4,z60,z108,z6]),(1,[z1,z2,z3,z4,z459,z8]),(0,[z1,z2,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z47,z93])],[(0,[z138,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z686,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z687,z6]),(0,[z538,z1,z2,z3,z4,z8,z6]),(1,[z1,z2,z11,z3,z4,z108]),(0,[z1,z2,z688,z3,z4,z8,z6]),(0,[z1,z2,z277,z3,z4,z8,z6])],[(0,[z1,z2,z689,z3,z4,z8,z6]),(0,[z690,z1,z2,z3,z4,z8,z6]),(0,[z146,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z88,z3,z4,z8,z16]),(0,[z1,z2,z11,z9,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z6,z691]),(0,[z1,z2,z3,z4,z8,z692,z6])],[(0,[z78,z1,z2,z3,z4,z443,z6]),(0,[z18,z1,z26,z3,z4,z8,z6]),(0,[z1,z2,z4,z8,z255,z6,z16]),(0,[z1,z2,z3,z4,z693,z8,z6]),(0,[z1,z2,z4,z8,z70,z6,z12])]],
   [[(0,[z1,z392,z2,z3,z4,z8,z6]),(0,[z694,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z695,z3,z4,z8,z6]),(0,[z1,z2,z3,z10,z4,z8,z16])],[(0,[z696,z1,z2,z3,z4,z8,z6]),(0,[z1,z149,z2,z11,z3,z4,z6])],[(0,[z1,z2,z3,z4,z697,z8,z6])],[(0,[z251,z1,z2,z85,z4,z8,z6]),(0,[z1,z118,z2,z3,z4,z8,z188]),(0,[z1,z2,z3,z4,z8,z622,z16]),(1,[z1,z2,z3,z4,z8,z153]),(0,[z1,z2,z3,z698,z4,z8,z6]),(0,[z1,z2,z3,z4,z468,z8,z6])],[(0,[z217,z2,z83,z3,z4,z8,z6]),(0,[z1,z127,z2,z11,z3,z4,z8]),(0,[z217,z2,z85,z3,z4,z8,z6]),(0,[z138,z1,z2,z3,z15,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z699]),(1,[z1,z118,z2,z11,z3,z4]),(0,[z1,z2,z106,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z92,z8,z6]),(0,[z1,z2,z11,z3,z4,z6,z216])],[(0,[z1,z2,z3,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z22,z8,z128]),(0,[z1,z2,z3,z4,z275,z8,z16]),(0,[z1,z2,z3,z4,z8,z700,z6]),(0,[z1,z397,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z63,z4,z8,z16]),(0,[z1,z2,z3,z701,z4,z8,z6]),(0,[z1,z2,z11,z3,z63,z4,z8]),(0,[z18,z1,z2,z3,z110,z8,z6]),(0,[z1,z2,z3,z702,z4,z8,z6]),(0,[z1,z144,z2,z3,z4,z8,z16])],[(0,[z78,z1,z398,z3,z4,z8,z6]),(0,[z1,z2,z3,z703,z4,z8,z6]),(0,[z1,z2,z3,z4,z704,z8,z6]),(0,[z1,z2,z3,z705,z4,z8,z6]),(0,[z1,z118,z2,z3,z4,z180,z6]),(0,[z1,z2,z3,z4,z706,z8,z6]),(0,[z1,z2,z11,z3,z4,z108,z6]),(0,[z1,z2,z41,z3,z4,z8,z172])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z20,z83,z3,z4,z8,z6]),(0,[z1,z148,z3,z4,z8,z47]),(0,[z1,z33,z3,z4,z8,z47]),(0,[z1,z2,z3,z4,z8,z707]),(0,[z1,z2,z708,z4,z8,z6]),(0,[z1,z322,z467,z3,z4,z8])],[(0,[z1,z2,z3,z4,z8,z709]),(0,[z1,z293,z2,z11,z3,z4])],[(0,[z1,z2,z3,z4,z8,z710]),(0,[z288,z2,z3,z4,z22,z8])],[(0,[z1,z2,z3,z4,z8,z711]),(0,[z1,z2,z315,z3,z46,z6])],[(0,[z130,z83,z3,z4,z8,z47]),(0,[z1,z2,z3,z712,z4,z8]),(0,[z1,z2,z713,z4,z8,z6]),(0,[z1,z2,z3,z4,z22,z443]),(0,[z1,z2,z4,z8,z714,z16]),(0,[z1,z613,z3,z4,z8,z16])],[(0,[z1,z2,z3,z4,z22,z139]),(0,[z199,z1,z3,z4,z8,z715])],[(0,[z1,z2,z716,z3,z4,z6]),(0,[z1,z2,z11,z3,z4,z444])],[],[(0,[z288,z2,z3,z4,z64,z6]),(0,[z717,z2,z3,z4,z8,z6]),(0,[z1,z2,z287,z287,z3,z4]),(0,[z1,z2,z3,z4,z153,z91])],[(0,[z1,z2,z3,z4,z718,z6]),(0,[z1,z2,z11,z3,z4,z719])],[(0,[z1,z2,z3,z110,z248,z6]),(0,[z1,z2,z3,z4,z8,z720]),(0,[z1,z3,z4,z8,z16,z412]),(0,[z1,z2,z3,z4,z8,z721])],[(0,[z223,z2,z85,z4,z8,z6]),(0,[z1,z2,z3,z722,z4,z8]),(0,[z74,z1,z2,z106,z4,z8]),(0,[z1,z2,z287,z3,z4,z180]),(0,[z1,z2,z106,z11,z4,z8])],[(0,[z1,z2,z3,z4,z723,z6]),(0,[z1,z2,z11,z147,z4,z108]),(0,[z1,z398,z3,z4,z443,z6]),(0,[z1,z2,z3,z79,z8,z622]),(0,[z1,z2,z3,z4,z724,z8])],[(0,[z1,z2,z3,z4,z725,z6]),(0,[z1,z2,z11,z3,z726,z8])],[(0,[z1,z2,z458,z4,z8,z6]),(0,[z1,z2,z727,z4,z8,z6]),(0,[z1,z2,z11,z3,z4,z677]),(0,[z1,z2,z728,z3,z4,z16]),(0,[z1,z2,z3,z4,z729,z216])],[(0,[z1,z2,z3,z97,z4,z47]),(0,[z1,z2,z3,z4,z8,z730]),(0,[z1,z2,z3,z4,z91,z145])]],
   [[(0,[z731,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z732]),(0,[z1,z2,z55,z4,z8,z163])],[(0,[z1,z2,z51,z4,z22,z8]),(0,[z1,z2,z240,z4,z108,z6]),(0,[z1,z2,z40,z4,z19,z154])],[(0,[z84,z127,z3,z4,z8,z6]),(0,[z223,z2,z3,z4,z8,z320]),(0,[z1,z2,z11,z3,z4,z145]),(0,[z2,z733,z3,z4,z8,z6])],[(0,[z1,z3,z4,z8,z734,z6]),(0,[z1,z2,z287,z3,z4,z337]),(0,[z1,z2,z106,z287,z3,z4]),(0,[z1,z2,z3,z8,z172,z735])],[(0,[z2,z3,z4,z8,z211,z6]),(0,[z146,z2,z3,z4,z8,z128]),(0,[z1,z736,z27,z4,z8,z6]),(0,[z1,z26,z2,z287,z3,z4]),(0,[z1,z2,z737,z3,z4,z8]),(0,[z1,z2,z4,z738,z8,z6]),(0,[z1,z2,z4,z8,z739,z16]),(0,[z1,z2,z740,z4,z8,z6])],[(1,[z1,z2,z106,z287,z4])],[(0,[z1,z2,z741,z4,z8,z6]),(0,[z1,z2,z742,z4,z8,z6]),(0,[z1,z2,z174,z3,z30,z8])],[],[(0,[z1,z2,z743,z3,z4,z8]),(0,[z1,z2,z11,z156,z4,z8]),(0,[z744,z2,z3,z4,z8,z6])],[(0,[z1,z2,z745,z4,z8,z16]),(0,[z1,z2,z746,z4,z8,z6])],[(0,[z1,z2,z156,z4,z22,z8]),(0,[z1,z2,z43,z3,z4,z6]),(0,[z1,z2,z41,z212,z4,z8]),(0,[z1,z2,z3,z79,z8,z735])],[(0,[z1,z2,z4,z747,z8,z6]),(0,[z1,z2,z3,z4,z459,z8]),(0,[z1,z2,z287,z4,z255,z6])],[(0,[z1,z748,z3,z4,z8,z6]),(1,[z1,z736,z4,z8,z6]),(0,[z2,z3,z4,z8,z749,z6]),(0,[z1,z2,z3,z8,z750,z16])],[(0,[z1,z2,z3,z4,z8,z751]),(0,[z84,z127,z3,z4,z8,z226]),(0,[z1,z127,z2,z287,z3,z4]),(0,[z1,z2,z3,z4,z8,z752]),(0,[z1,z2,z753,z3,z4,z8]),(0,[z1,z2,z754,z4,z8,z16]),(0,[z1,z2,z9,z755,z8,z6]),(0,[z1,z2,z11,z3,z4,z228])],[(0,[z1,z2,z3,z4,z756,z8]),(0,[z1,z2,z287,z3,z4,z75]),(0,[z1,z2,z4,z8,z255,z47]),(0,[z1,z2,z3,z4,z22,z203]),(0,[z1,z2,z3,z4,z8,z757])],[(0,[z1,z2,z758,z3,z4,z8]),(0,[z1,z2,z759,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z760]),(0,[z1,z2,z106,z4,z8,z393]),(0,[z1,z2,z3,z755,z8,z6]),(0,[z1,z2,z3,z119,z81,z121])]],
   [[(0,[z1,z2,z689,z4,z108,z6]),(0,[z78,z2,z43,z3,z8,z6]),(0,[z1,z2,z287,z4,z8,z255]),(0,[z1,z2,z3,z4,z8,z761])],[(0,[z1,z2,z3,z4,z8,z762]),(0,[z694,z2,z147,z4,z8,z6]),(0,[z1,z2,z763,z4,z8,z6]),(0,[z1,z219,z4,z19,z8,z6]),(1,[z1,z2,z3,z764,z6])],[(0,[z1,z765,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z153])],[(0,[z17,z2,z3,z207,z5,z6]),(0,[z1,z118,z2,z11,z3,z4])],[(0,[z1,z127,z467,z3,z4,z8])],[(0,[z1,z2,z766,z3,z4,z8]),(0,[z1,z2,z184,z4,z8,z206]),(0,[z1,z2,z116,z3,z8,z16]),(0,[z1,z2,z150,z4,z22,z8]),(0,[z1,z2,z3,z4,z195,z180]),(0,[z1,z2,z287,z3,z4,z393])],[(0,[z1,z2,z106,z4,z8,z12])],[(0,[z1,z2,z767,z3,z4,z8]),(0,[z217,z2,z85,z4,z8,z16]),(0,[z1,z2,z309,z3,z8,z234]),(0,[z1,z3,z4,z8,z193,z47])],[(0,[z1,z2,z3,z4,z8,z768]),(0,[z1,z59,z150,z275,z8,z6]),(0,[z1,z2,z3,z4,z8,z769])],[(0,[z1,z2,z770,z3,z4,z8]),(0,[z1,z2,z3,z4,z771,z8]),(0,[z1,z2,z61,z99,z8,z47]),(0,[z1,z2,z3,z4,z271,z47])],[(0,[z1,z2,z3,z4,z8,z772]),(0,[z1,z2,z773,z3,z4,z8]),(0,[z1,z2,z287,z3,z4,z47]),(0,[z1,z2,z301,z287,z3,z4])],[(0,[z1,z2,z106,z4,z8,z255]),(0,[z1,z2,z315,z3,z46,z16]),(0,[z1,z2,z3,z4,z774,z8])],[(0,[z1,z2,z3,z4,z775,z8]),(0,[z217,z2,z776,z4,z8,z6]),(0,[z1,z2,z3,z777,z8,z6]),(0,[z1,z26,z11,z87,z4,z8]),(0,[z1,z2,z249,z4,z8,z255]),(0,[z1,z2,z287,z3,z4,z12])],[(0,[z0,z2,z3,z4,z64,z47]),(0,[z1,z2,z778,z3,z4,z8])],[(0,[z1,z2,z779,z3,z4,z8]),(0,[z1,z149,z3,z4,z60,z177])],[(0,[z1,z50,z3,z4,z8,z16]),(0,[z1,z2,z780,z4,z8,z6]),(0,[z1,z2,z781,z3,z4,z8])]],
   [[(0,[z1,z2,z3,z4,z782,z8]),(0,[z251,z2,z11,z147,z4,z8]),(0,[z1,z2,z3,z4,z8,z783]),(0,[z1,z2,z784,z3,z4,z8]),(0,[z1,z2,z61,z287,z3,z4])],[(0,[z1,z2,z11,z3,z4,z627]),(0,[z1,z2,z287,z3,z4,z64]),(0,[z1,z2,z287,z3,z4,z255]),(0,[z1,z2,z11,z3,z4,z72])],[(0,[z1,z2,z106,z4,z8,z70])],[(0,[z1,z2,z3,z785,z8,z6]),(0,[z1,z2,z106,z287,z4,z6])],[],[(0,[z1,z2,z51,z4,z52,z6]),(0,[z1,z2,z301,z3,z4,z8]),(0,[z1,z2,z9,z10,z8,z6]),(0,[z1,z2,z467,z3,z4,z108]),(0,[z1,z2,z3,z4,z22,z520])],[(0,[z1,z2,z458,z4,z8,z16]),(0,[z17,z2,z11,z3,z4,z5])],[(0,[z2,z776,z3,z4,z8,z6]),(0,[z1,z2,z287,z9,z3,z4])],[(0,[z1,z2,z786,z4,z8,z6]),(0,[z18,z223,z27,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z787]),(0,[z1,z2,z4,z22,z316,z8]),(0,[z1,z2,z3,z4,z8,z788]),(0,[z1,z2,z287,z3,z4,z70])],[(0,[z78,z2,z11,z3,z15,z8]),(0,[z1,z2,z789,z4,z8,z6])],[(0,[z84,z127,z3,z4,z8,z16]),(0,[z1,z790,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z791,z6]),(0,[z1,z2,z792,z3,z4,z8]),(0,[z2,z3,z4,z64,z793,z6]),(0,[z1,z59,z3,z275,z8,z76]),(0,[z1,z2,z794,z4,z201,z8])],[(0,[z2,z156,z147,z4,z8,z6]),(0,[z1,z2,z51,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z795]),(0,[z38,z2,z3,z4,z295,z8]),(0,[z1,z26,z87,z4,z8,z161]),(0,[z2,z3,z4,z8,z211,z16]),(0,[z1,z2,z287,z796,z3,z4])],[(0,[z1,z2,z3,z4,z8,z797]),(0,[z1,z2,z798,z3,z4,z8]),(0,[z1,z2,z799,z4,z8,z6]),(0,[z1,z2,z315,z11,z3,z46])],[(0,[z1,z2,z3,z4,z8,z800]),(0,[z1,z2,z3,z4,z92,z12])],[(0,[z1,z2,z3,z4,z801,z8]),(0,[z1,z2,z802,z4,z8,z6]),(0,[z1,z2,z803,z3,z4,z8]),(0,[z1,z219,z3,z4,z8,z804])]],
   [[(0,[z1,z2,z805,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z806]),(0,[z74,z2,z265,z3,z4,z8]),(0,[z1,z2,z4,z807,z8,z6]),(0,[z1,z3,z808,z4,z8,z6]),(0,[z1,z219,z48,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z809])],[(0,[z1,z2,z43,z3,z4,z16])],[(0,[z1,z2,z810,z3,z4,z8]),(0,[z1,z2,z811,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z812]),(0,[z1,z2,z3,z4,z813,z6]),(0,[z1,z26,z87,z4,z8,z6]),(0,[z1,z2,z287,z4,z255,z16]),(0,[z1,z2,z4,z8,z16,z814])],[],[(0,[z1,z144,z3,z386,z8,z6]),(0,[z1,z2,z3,z4,z815,z6]),(0,[z1,z2,z3,z4,z8,z816]),(0,[z1,z3,z4,z8,z817,z6])],[(0,[z1,z2,z3,z8,z818,z6]),(0,[z1,z144,z2,z287,z3,z4]),(0,[z1,z2,z4,z819,z108,z6]),(0,[z1,z293,z3,z4,z201,z8])],[(0,[z1,z2,z377,z4,z8,z47]),(0,[z1,z2,z820,z3,z4,z248]),(0,[z1,z2,z411,z29,z4,z8]),(0,[z71,z1,z2,z287,z3,z4])],[(0,[z1,z2,z3,z4,z8,z821]),(0,[z138,z2,z3,z63,z8,z6])],[(0,[z251,z2,z147,z4,z22,z8]),(0,[z822,z2,z3,z4,z8,z6]),(0,[z1,z149,z411,z4,z8,z6])],[(0,[z1,z2,z3,z823,z8,z6]),(0,[z1,z149,z11,z3,z4,z60]),(0,[z1,z2,z11,z4,z316,z8]),(0,[z1,z2,z3,z4,z92,z70])],[(0,[z1,z824,z3,z4,z8,z6]),(0,[z1,z149,z11,z87,z3,z4]),(0,[z1,z219,z11,z3,z4,z8]),(0,[z1,z2,z11,z3,z4,z350])],[(0,[z1,z2,z3,z4,z825,z8])],[(0,[z1,z2,z3,z4,z8,z826])],[(0,[z2,z3,z4,z827,z8,z6])],[(0,[z127,z824,z3,z4,z8,z6]),(0,[z1,z2,z828,z3,z4,z8]),(0,[z1,z2,z3,z829,z4,z8]),(0,[z1,z2,z287,z3,z4,z830])]],
   [[(0,[z1,z2,z3,z4,z831,z6]),(0,[z1,z2,z3,z4,z832,z8])],[],[(0,[z1,z2,z3,z186,z22,z8])],[(0,[z1,z2,z3,z110,z8,z6]),(0,[z1,z2,z833,z3,z4,z8]),(0,[z1,z2,z106,z4,z8,z234])],[(0,[z1,z2,z3,z4,z443,z206])],[(0,[z1,z834,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z835,z8]),(0,[z1,z2,z3,z4,z836,z6]),(0,[z17,z2,z3,z4,z22,z5]),(0,[z1,z2,z3,z4,z8,z837])],[(0,[z2,z3,z4,z8,z838,z128]),(0,[z1,z2,z287,z3,z4,z8]),(0,[z1,z2,z287,z3,z119,z4]),(0,[z1,z2,z839,z287,z3,z4]),(0,[z1,z2,z61,z755,z8,z6]),(0,[z1,z2,z3,z4,z8,z103])],[(0,[z1,z2,z3,z4,z840,z6]),(0,[z1,z2,z841,z3,z4,z111]),(0,[z1,z2,z3,z4,z8,z842]),(0,[z1,z397,z301,z3,z4,z8])],[(1,[z1,z3,z843,z8,z6])],[(0,[z1,z118,z3,z4,z278,z6]),(0,[z1,z159,z3,z4,z8,z715]),(0,[z1,z2,z3,z4,z8,z844])],[(0,[z1,z2,z10,z297,z8,z6]),(0,[z1,z149,z467,z3,z4,z6]),(0,[z1,z118,z3,z4,z180,z188]),(0,[z1,z118,z2,z301,z3,z4])],[(0,[z1,z2,z3,z4,z8,z845]),(0,[z1,z2,z106,z287,z4,z16]),(0,[z1,z3,z4,z8,z142,z47])],[(0,[z1,z398,z3,z4,z8,z206]),(0,[z78,z2,z3,z15,z22,z8]),(0,[z1,z2,z759,z247,z4,z8]),(0,[z1,z2,z411,z4,z8,z47]),(0,[z1,z2,z3,z4,z8,z846])],[(0,[z17,z2,z3,z4,z793,z6]),(0,[z1,z2,z3,z4,z8,z847]),(0,[z1,z467,z3,z4,z180,z8]),(0,[z1,z2,z9,z10,z8,z16]),(0,[z1,z848,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z849]),(0,[z1,z2,z11,z3,z4,z492]),(0,[z1,z2,z850,z4,z8,z47]),(0,[z1,z2,z3,z4,z8,z851])],[(0,[z1,z2,z3,z4,z8,z852])]],
   [[(0,[z1,z2,z3,z4,z8,z853]),(0,[z1,z2,z854,z3,z8,z6]),(0,[z1,z2,z3,z4,z8,z855]),(0,[z1,z2,z3,z4,z8,z856])],[(0,[z1,z26,z89,z4,z8,z6]),(0,[z1,z2,z4,z203,z255,z6]),(0,[z1,z2,z3,z4,z8,z857])],[(0,[z1,z2,z3,z4,z858,z6]),(0,[z1,z2,z287,z55,z3,z4])],[(0,[z1,z2,z3,z4,z8,z859]),(0,[z223,z2,z3,z4,z111,z6]),(0,[z1,z2,z860,z287,z3,z4])],[(0,[z2,z776,z147,z4,z8,z6]),(0,[z1,z2,z51,z4,z8,z16]),(0,[z1,z2,z3,z4,z443,z47])],[(0,[z1,z2,z11,z3,z97,z4]),(0,[z1,z2,z411,z4,z111,z6]),(0,[z1,z2,z861,z4,z8,z47])],[(0,[z1,z2,z3,z4,z8,z862]),(0,[z1,z2,z863,z3,z4,z8])],[(0,[z1,z59,z2,z287,z3,z4]),(0,[z1,z2,z802,z4,z8,z16]),(0,[z1,z2,z3,z8,z764,z6]),(0,[z1,z864,z11,z3,z4,z8])],[(0,[z1,z2,z357,z4,z22,z8]),(0,[z1,z3,z4,z706,z8,z16]),(0,[z1,z2,z4,z807,z8,z16]),(0,[z1,z2,z55,z4,z8,z255]),(0,[z1,z2,z40,z4,z19,z47])],[(0,[z1,z149,z3,z4,z22,z60])],[(0,[z18,z1,z2,z287,z3,z4]),(0,[z1,z219,z3,z4,z22,z8])],[(0,[z1,z2,z3,z865,z8,z6]),(0,[z78,z2,z3,z86,z15,z8]),(0,[z1,z2,z3,z207,z8,z6]),(0,[z1,z2,z3,z97,z4,z22]),(0,[z1,z2,z866,z4,z8,z6]),(0,[z1,z26,z87,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z867]),(0,[z1,z2,z811,z4,z8,z16])],[(0,[z1,z398,z3,z4,z8,z47]),(0,[z1,z2,z3,z4,z8,z868]),(0,[z1,z2,z11,z3,z4,z153])],[(0,[z1,z2,z3,z4,z8,z869]),(0,[z288,z2,z315,z3,z8,z6])],[(0,[z1,z2,z3,z4,z870,z8]),(0,[z1,z149,z2,z11,z3,z4])],[(0,[z251,z2,z580,z147,z4,z8]),(0,[z1,z2,z871,z3,z8,z6]),(0,[z1,z2,z55,z4,z8,z70])]],
   [[(0,[z1,z2,z11,z3,z4,z267]),(0,[z288,z2,z3,z4,z8,z6]),(0,[z138,z2,z3,z63,z8,z16]),(0,[z1,z2,z4,z8,z872,z6]),(0,[z1,z2,z3,z4,z195,z8]),(0,[z1,z2,z48,z4,z108,z47])],[(0,[z18,z1,z4,z601,z8,z6])],[(0,[z1,z2,z3,z4,z8,z873]),(0,[z1,z2,z3,z4,z8,z471])],[(0,[z1,z638,z2,z11,z3,z4]),(0,[z1,z3,z4,z8,z874,z6])],[(0,[z1,z2,z3,z4,z8,z875]),(0,[z1,z2,z247,z4,z8,z47]),(0,[z1,z2,z3,z4,z8,z804])],[(0,[z1,z148,z51,z4,z8,z6]),(0,[z1,z2,z11,z287,z3,z4]),(0,[z1,z3,z4,z22,z8,z193])],[(0,[z1,z2,z3,z81,z244,z6]),(0,[z38,z2,z178,z3,z4,z8]),(0,[z1,z2,z29,z3,z4,z108]),(0,[z1,z2,z3,z4,z8,z876])],[(0,[z1,z2,z877,z4,z8,z6]),(0,[z1,z2,z11,z3,z4,z45]),(0,[z1,z2,z3,z79,z592,z8]),(0,[z1,z2,z3,z186,z248,z6]),(0,[z1,z149,z3,z4,z111,z6]),(0,[z1,z59,z3,z275,z22,z8]),(0,[z1,z2,z196,z3,z4,z22])],[(0,[z18,z1,z620,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z878]),(0,[z1,z2,z4,z8,z879,z12])],[(0,[z78,z2,z336,z3,z8,z6])],[(0,[z1,z2,z51,z4,z8,z169])],[(0,[z1,z2,z880,z3,z4,z6]),(0,[z1,z2,z3,z110,z8,z16]),(0,[z1,z2,z3,z4,z881,z8]),(0,[z1,z2,z150,z99,z8,z6]),(0,[z1,z439,z3,z4,z8,z47]),(0,[z1,z2,z3,z4,z8,z735])],[(0,[z1,z2,z3,z4,z882,z6]),(0,[z1,z2,z3,z4,z8,z883]),(0,[z1,z2,z3,z884,z4,z8]),(0,[z1,z2,z3,z4,z885,z8])],[(0,[z824,z83,z3,z4,z8,z6]),(0,[z2,z886,z3,z4,z8,z6])],[(0,[z1,z2,z4,z316,z8,z6]),(0,[z1,z149,z3,z4,z60,z6]),(0,[z1,z2,z301,z3,z4,z596]),(1,[z1,z2,z3,z4,z729])],[(0,[z152,z2,z85,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z887]),(0,[z888,z2,z3,z4,z8,z6]),(0,[z1,z2,z555,z4,z8,z70]),(0,[z1,z2,z11,z3,z4,z271])]],
   [[(0,[z1,z2,z11,z3,z4,z8]),(0,[z1,z2,z147,z110,z8,z6]),(0,[z1,z2,z3,z4,z8,z889]),(0,[z78,z2,z3,z15,z52,z6]),(0,[z1,z2,z287,z3,z4,z128])],[(0,[z1,z2,z3,z4,z890,z6]),(0,[z1,z118,z2,z891,z3,z4])],[(0,[z1,z2,z3,z110,z8,z320]),(0,[z1,z2,z3,z110,z8,z321]),(0,[z1,z2,z29,z3,z4,z19]),(0,[z1,z2,z3,z4,z8,z892])],[(0,[z1,z2,z88,z3,z176,z8]),(0,[z18,z1,z114,z4,z8,z6]),(0,[z1,z2,z3,z4,z893,z8]),(0,[z1,z2,z287,z3,z7,z4])],[(0,[z1,z2,z287,z3,z894,z4])],[(0,[z1,z2,z11,z3,z702,z4]),(0,[z1,z2,z3,z4,z8,z895]),(0,[z1,z2,z3,z4,z8,z896])],[(0,[z392,z2,z3,z4,z111,z6]),(0,[z18,z1,z27,z110,z8,z6]),(0,[z1,z2,z3,z897,z8,z6]),(0,[z1,z2,z411,z11,z4,z8]),(0,[z1,z2,z4,z201,z8,z739]),(0,[z1,z2,z287,z3,z4,z22]),(0,[z1,z2,z3,z4,z8,z898]),(0,[z1,z2,z3,z4,z8,z899])],[(0,[z78,z2,z3,z15,z8,z6]),(0,[z2,z3,z4,z793,z5,z6]),(0,[z1,z2,z4,z8,z6,z900]),(0,[z1,z2,z106,z4,z8,z622]),(0,[z1,z2,z3,z4,z8,z901])],[(0,[z1,z2,z156,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z902]),(0,[z1,z372,z3,z4,z8,z16]),(0,[z1,z219,z285,z3,z4,z8]),(0,[z1,z2,z359,z4,z8,z12])],[(0,[z1,z118,z301,z3,z4,z180]),(0,[z1,z2,z4,z203,z255,z16])],[(0,[z1,z2,z3,z4,z903,z8]),(0,[z1,z2,z3,z4,z111,z47]),(0,[z1,z2,z333,z4,z19,z6])],[(0,[z1,z2,z3,z4,z8,z904]),(0,[z1,z2,z3,z905,z8,z6]),(0,[z1,z2,z3,z4,z8,z300])],[(0,[z1,z2,z906,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z907]),(0,[z1,z2,z3,z4,z8,z908]),(0,[z1,z2,z3,z4,z8,z909]),(0,[z910,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z911,z6]),(0,[z1,z2,z912,z3,z4,z6]),(0,[z1,z2,z3,z4,z8,z913]),(0,[z1,z2,z3,z4,z914,z8]),(0,[z915,z2,z3,z4,z8,z6]),(0,[z1,z2,z287,z3,z4,z622]),(0,[z1,z2,z11,z4,z8,z255])],[(0,[z1,z454,z2,z11,z3,z4]),(0,[z1,z2,z3,z30,z8,z172])],[(0,[z1,z83,z467,z3,z4,z8]),(0,[z1,z2,z3,z4,z916,z8]),(0,[z18,z1,z27,z4,z22,z8]),(0,[z1,z614,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z917])]],
   [[(0,[z1,z2,z3,z918,z4,z6]),(0,[z1,z3,z736,z4,z8,z6]),(0,[z1,z2,z4,z8,z6,z879])],[(0,[z1,z2,z3,z4,z8,z919]),(0,[z2,z3,z4,z8,z6,z920]),(0,[z1,z921,z3,z4,z8,z193])],[(0,[z84,z127,z377,z4,z8,z6]),(0,[z1,z2,z922,z3,z4,z8]),(0,[z138,z2,z3,z827,z8,z6]),(0,[z1,z2,z3,z4,z8,z923]),(0,[z1,z2,z924,z3,z4,z8]),(0,[z1,z2,z2,z287,z3,z4])],[(0,[z1,z2,z3,z4,z925,z8]),(0,[z1,z2,z3,z4,z8,z926]),(0,[z1,z2,z3,z207,z8,z16]),(0,[z1,z2,z287,z3,z4,z5]),(0,[z1,z2,z150,z4,z8,z6]),(0,[z323,z1,z2,z287,z3,z4]),(0,[z1,z2,z3,z134,z8,z141])],[(0,[z1,z2,z11,z3,z4,z52]),(0,[z1,z2,z3,z4,z927,z8])],[(0,[z1,z148,z3,z4,z22,z8]),(0,[z138,z2,z3,z452,z8,z6]),(0,[z1,z2,z315,z3,z704,z6]),(0,[z1,z2,z357,z4,z8,z928]),(0,[z1,z467,z3,z4,z8,z47])],[(0,[z1,z2,z11,z3,z4,z376])],[(0,[z1,z106,z4,z8,z47,z16]),(0,[z1,z2,z929,z4,z22,z8])],[(0,[z1,z2,z3,z4,z8,z930]),(0,[z288,z2,z3,z4,z8,z16]),(0,[z1,z2,z931,z3,z4,z8])],[(0,[z1,z2,z932,z3,z4,z8]),(0,[z1,z148,z3,z4,z8,z933]),(0,[z1,z2,z934,z4,z8,z6]),(0,[z1,z2,z3,z4,z935,z8]),(0,[z1,z2,z3,z4,z936,z6]),(0,[z1,z2,z3,z4,z937,z6])],[(0,[z1,z2,z3,z4,z938,z6]),(0,[z1,z2,z116,z3,z443,z6]),(0,[z1,z2,z939,z4,z8,z16])],[(0,[z1,z2,z3,z4,z940,z6]),(0,[z288,z2,z3,z119,z4,z6])],[(0,[z1,z2,z287,z3,z4,z234])],[(0,[z1,z2,z3,z4,z941,z6]),(0,[z223,z2,z3,z4,z8,z47]),(0,[z1,z2,z11,z3,z4,z455])],[(0,[z1,z2,z3,z4,z8,z942]),(0,[z1,z26,z736,z4,z8,z6]),(0,[z31,z1,z2,z287,z3,z4]),(0,[z1,z2,z3,z4,z22,z271])],[(0,[z1,z2,z3,z4,z22,z8]),(0,[z1,z3,z4,z180,z943,z6]),(0,[z1,z2,z3,z4,z8,z415])]],
   [[(0,[z1,z2,z3,z4,z8,z49]),(0,[z17,z2,z116,z3,z4,z6]),(1,[z2,z3,z4,z8,z838]),(0,[z1,z2,z4,z19,z340,z6]),(0,[z1,z2,z411,z4,z108,z6]),(0,[z1,z2,z88,z3,z8,z487])],[(0,[z1,z2,z55,z4,z92,z70]),(0,[z1,z2,z351,z464,z4,z8])],[(0,[z1,z460,z3,z4,z180,z6])],[(0,[z1,z2,z3,z4,z8,z933]),(0,[z1,z944,z3,z4,z8,z6]),(0,[z1,z2,z170,z3,z8,z93]),(0,[z1,z2,z4,z8,z6,z945])],[(0,[z1,z2,z3,z4,z8,z946]),(0,[z1,z2,z3,z4,z947,z8])],[(0,[z1,z2,z3,z4,z8,z948]),(0,[z1,z2,z3,z4,z8,z188]),(0,[z1,z149,z2,z301,z3,z4]),(0,[z1,z2,z3,z764,z46,z6])],[(0,[z1,z26,z2,z4,z8,z300]),(0,[z1,z2,z3,z4,z8,z76]),(0,[z1,z149,z3,z4,z60,z16]),(0,[z1,z2,z4,z316,z8,z16])],[(0,[z17,z2,z3,z701,z4,z6]),(0,[z949,z2,z3,z4,z8,z6])],[(0,[z199,z1,z2,z287,z3,z4]),(0,[z1,z2,z80,z4,z8,z171])],[(0,[z1,z2,z3,z554,z207,z8]),(0,[z1,z2,z287,z3,z4,z275]),(0,[z1,z2,z3,z4,z890,z16]),(0,[z1,z2,z287,z467,z3,z4]),(0,[z1,z2,z3,z4,z8,z950])],[(0,[z1,z2,z3,z4,z8,z951]),(0,[z1,z2,z11,z3,z4,z693]),(0,[z1,z2,z3,z4,z8,z952]),(0,[z1,z2,z3,z4,z8,z953]),(0,[z2,z315,z3,z211,z46,z6])],[(0,[z1,z148,z3,z4,z8,z873]),(0,[z1,z2,z3,z954,z4,z8])],[(0,[z1,z2,z3,z4,z8,z955]),(1,[z1,z3,z4,z8,z715]),(0,[z1,z2,z40,z4,z819,z6]),(0,[z1,z2,z464,z4,z8,z70])],[(0,[z78,z2,z3,z704,z8,z6]),(0,[z1,z2,z956,z3,z4,z8])],[(0,[z1,z2,z3,z4,z8,z957]),(0,[z1,z2,z3,z4,z958,z6]),(0,[z1,z59,z357,z275,z8,z6]),(0,[z1,z2,z3,z4,z8,z107])],[(0,[z1,z2,z11,z85,z4,z108]),(0,[z78,z2,z3,z15,z8,z16]),(0,[z288,z2,z3,z4,z5,z6]),(0,[z1,z279,z3,z4,z8,z16]),(0,[z1,z2,z10,z755,z8,z6]),(0,[z1,z2,z959,z3,z4,z8])]],
   [[(0,[z1,z2,z156,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z960]),(0,[z1,z2,z961,z4,z8,z6]),(0,[z138,z2,z11,z3,z63,z8]),(0,[z18,z1,z27,z186,z8,z6]),(0,[z1,z2,z962,z4,z8,z6]),(0,[z1,z2,z411,z4,z459,z8]),(1,[z1,z2,z4,z8,z879]),(0,[z1,z2,z3,z4,z8,z963]),(0,[z1,z2,z11,z3,z4,z22])],[(1,[z2,z776,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z964]),(0,[z1,z864,z3,z4,z8,z6]),(0,[z1,z2,z4,z755,z8,z6]),(0,[z1,z2,z3,z4,z108,z154])],[(0,[z78,z2,z184,z15,z8,z6]),(0,[z1,z2,z48,z11,z4,z108])],[(0,[z1,z2,z965,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z966]),(0,[z1,z2,z3,z4,z22,z52])],[(0,[z18,z1,z27,z4,z248,z6])],[(0,[z220,z2,z3,z4,z64,z6]),(0,[z1,z2,z3,z4,z8,z967]),(0,[z1,z2,z939,z4,z8,z6])],[(0,[z1,z3,z843,z275,z8,z6]),(1,[z1,z2,z287,z4,z255]),(0,[z1,z2,z968,z4,z8,z6])],[(0,[z251,z2,z147,z4,z8,z6]),(0,[z1,z2,z116,z3,z8,z47]),(0,[z1,z2,z969,z4,z22,z8])],[(0,[z1,z2,z41,z4,z8,z171]),(1,[z1,z2,z3,z8,z735])],[(0,[z217,z2,z85,z4,z8,z47]),(0,[z1,z148,z11,z3,z4,z8]),(0,[z1,z2,z970,z4,z8,z6]),(0,[z74,z1,z2,z287,z3,z4]),(0,[z1,z2,z971,z3,z4,z8]),(0,[z1,z2,z106,z4,z22,z8]),(0,[z1,z972,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z973,z6]),(0,[z1,z3,z4,z974,z8,z6])],[(0,[z1,z2,z3,z4,z8,z975]),(0,[z1,z2,z976,z3,z4,z6]),(0,[z1,z2,z150,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z977]),(0,[z1,z2,z3,z4,z8,z978])],[(0,[z1,z2,z979,z3,z4,z8])],[(0,[z130,z83,z11,z3,z4,z8]),(0,[z1,z2,z11,z247,z4,z8]),(0,[z1,z2,z3,z4,z8,z177]),(0,[z1,z219,z3,z4,z8,z16]),(0,[z1,z2,z315,z3,z46,z47]),(0,[z1,z2,z285,z3,z4,z8]),(0,[z1,z2,z3,z4,z153,z271])],[(0,[z1,z2,z85,z110,z8,z6]),(0,[z1,z2,z980,z287,z3,z4]),(0,[z1,z2,z4,z22,z8,z255]),(0,[z1,z2,z713,z4,z8,z47])],[(0,[z1,z2,z580,z3,z4,z8]),(0,[z1,z390,z3,z4,z8,z47])]],
   [[(0,[z1,z2,z3,z4,z981,z6]),(0,[z1,z2,z11,z3,z4,z507]),(0,[z78,z148,z3,z15,z8,z6]),(0,[z392,z2,z3,z4,z8,z47]),(0,[z1,z2,z3,z186,z8,z6]),(0,[z1,z3,z4,z8,z47,z16]),(0,[z1,z2,z3,z4,z8,z982])],[(0,[z1,z2,z3,z4,z936,z16]),(0,[z1,z2,z983,z3,z4,z8])],[(0,[z1,z2,z984,z3,z4,z8]),(0,[z1,z219,z147,z4,z8,z6]),(0,[z1,z985,z3,z4,z8,z6]),(0,[z1,z118,z3,z4,z180,z6]),(0,[z1,z3,z4,z8,z986,z6])],[(0,[z1,z26,z403,z4,z8,z6]),(0,[z1,z2,z287,z3,z4,z99]),(0,[z1,z2,z11,z3,z4,z653])],[(0,[z1,z2,z3,z97,z4,z883]),(0,[z1,z2,z3,z4,z248,z6]),(0,[z1,z2,z3,z4,z987,z8]),(0,[z1,z566,z3,z4,z8,z47]),(0,[z1,z2,z3,z4,z8,z988]),(0,[z1,z2,z3,z4,z8,z989])],[(0,[z1,z2,z3,z990,z8,z6]),(0,[z78,z2,z3,z15,z8,z169]),(0,[z1,z2,z991,z43,z3,z4]),(0,[z17,z2,z3,z4,z5,z6])],[],[(0,[z1,z2,z992,z4,z8,z6]),(0,[z1,z2,z3,z4,z725,z47]),(0,[z1,z2,z3,z4,z8,z993])],[(0,[z1,z2,z4,z994,z8,z6]),(0,[z1,z2,z3,z4,z8,z995]),(0,[z1,z2,z458,z4,z8,z47])],[(0,[z1,z2,z996,z3,z4,z8]),(0,[z1,z2,z997,z3,z4,z8]),(0,[z1,z2,z11,z3,z4,z596]),(0,[z1,z2,z3,z4,z8,z409])],[(0,[z1,z2,z3,z4,z998,z6]),(0,[z217,z1,z2,z287,z3,z4]),(0,[z1,z2,z184,z4,z22,z8]),(0,[z288,z2,z3,z4,z443,z6]),(0,[z1,z2,z3,z371,z8,z172])],[(0,[z1,z2,z999,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z1000]),(0,[z78,z2,z3,z97,z15,z6]),(0,[z1,z2,z3,z4,z8,z1001])],[(0,[z84,z127,z3,z4,z8,z47]),(0,[z1,z2,z1002,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z928]),(0,[z1,z2,z3,z4,z195,z472]),(0,[z1,z11,z3,z4,z8,z193])],[(0,[z130,z1,z2,z287,z3,z4]),(0,[z1,z2,z3,z4,z6,z1003]),(0,[z1,z2,z116,z3,z554,z8]),(0,[z1,z2,z61,z110,z8,z6]),(0,[z1,z3,z364,z4,z8,z16])],[(0,[z1,z2,z3,z4,z1004,z443]),(0,[z0,z1,z2,z287,z3,z4])],[]],
   [[(0,[z1,z2,z3,z4,z1005,z8]),(0,[z1,z361,z3,z21,z8,z6]),(0,[z1,z2,z88,z3,z8,z735])],[(0,[z1,z2,z40,z4,z22,z19]),(0,[z1,z2,z55,z4,z271,z70])],[(0,[z1,z2,z116,z11,z3,z8]),(0,[z1,z2,z3,z4,z8,z1006]),(0,[z1,z2,z3,z4,z22,z533])],[(0,[z0,z1,z2,z116,z3,z6])],[(0,[z1,z2,z767,z377,z4,z8]),(0,[z1,z2,z43,z3,z4,z47]),(0,[z138,z1,z2,z287,z3,z4]),(0,[z538,z2,z3,z4,z8,z75]),(0,[z1,z118,z11,z3,z4,z180]),(0,[z1,z2,z3,z4,z8,z1007])],[(0,[z130,z824,z3,z4,z8,z6]),(0,[z2,z824,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z1008,z6]),(0,[z1,z2,z1009,z3,z4,z8]),(0,[z1,z2,z3,z4,z1010,z8])],[(0,[z1,z2,z11,z3,z207,z8]),(0,[z74,z2,z3,z4,z8,z128]),(0,[z1,z2,z3,z4,z1011,z8]),(0,[z18,z1,z149,z11,z3,z4]),(0,[z1,z2,z357,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1012]),(0,[z1,z2,z287,z3,z4,z201])],[(0,[z84,z548,z3,z4,z8,z6]),(0,[z1013,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z1014]),(0,[z1,z219,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1015])],[(0,[z1,z2,z1016,z3,z4,z8]),(0,[z1,z2,z1017,z3,z4,z8]),(0,[z1,z2,z1018,z4,z8,z6]),(0,[z1,z2,z51,z4,z443,z6]),(0,[z1,z2,z1019,z3,z4,z8])],[(0,[z1,z2,z1020,z4,z8,z6]),(0,[z1,z2,z3,z86,z97,z4])],[(0,[z1,z2,z1021,z3,z4,z8])],[(0,[z130,z83,z3,z4,z22,z8]),(0,[z38,z1,z2,z3,z4,z92]),(0,[z1,z2,z467,z3,z4,z8])],[(0,[z1,z2,z3,z4,z8,z1022]),(0,[z1,z2,z287,z3,z4,z177]),(0,[z1,z2,z3,z4,z8,z1023])],[(0,[z1,z2,z3,z4,z1024,z8]),(0,[z1,z447,z3,z4,z8,z47])],[(0,[z251,z2,z776,z4,z8,z6]),(0,[z251,z2,z147,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z1025]),(0,[z656,z1,z2,z315,z3,z6]),(0,[z38,z2,z3,z4,z8,z838]),(0,[z1,z2,z1026,z3,z4,z8]),(0,[z538,z2,z3,z4,z8,z200])]],
   [[(0,[z1,z2,z3,z4,z1027,z6]),(0,[z17,z2,z3,z4,z443,z6]),(0,[z1028,z2,z3,z4,z8,z6])],[(0,[z1,z398,z51,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1029]),(0,[z74,z2,z3,z4,z8,z129]),(0,[z1,z2,z88,z3,z197,z8])],[(0,[z1,z2,z3,z4,z973,z16]),(0,[z1,z2,z1030,z3,z4,z8])],[(0,[z1,z2,z3,z4,z8,z1031]),(0,[z1,z2,z3,z4,z6,z1032]),(0,[z1,z2,z976,z3,z4,z16]),(0,[z2,z3,z4,z8,z16,z920]),(0,[z1,z276,z3,z4,z8,z16]),(0,[z1,z2,z3,z1033,z4,z8])],[(0,[z1,z2,z3,z4,z793,z6]),(0,[z1,z2,z41,z4,z8,z161])],[(0,[z1,z59,z3,z275,z8,z6]),(0,[z1,z2,z3,z119,z764,z6])],[(0,[z0,z2,z11,z3,z4,z64])],[(0,[z1,z149,z29,z3,z4,z60]),(0,[z1,z2,z29,z4,z316,z8])],[(0,[z1,z2,z3,z186,z8,z16]),(0,[z1,z2,z3,z4,z8,z1034]),(0,[z1,z2,z3,z4,z981,z16]),(1,[z1,z219,z11,z3,z4])],[(0,[z1035,z2,z3,z4,z8,z6])],[(0,[z1,z2,z1036,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1037]),(0,[z1,z118,z3,z4,z180,z16]),(0,[z1,z3,z4,z8,z715,z6]),(0,[z1,z2,z48,z285,z4,z108]),(0,[z1,z2,z740,z467,z4,z8])],[],[(0,[z1,z2,z11,z3,z4,z531]),(0,[z1,z2,z3,z4,z248,z16]),(0,[z1,z2,z1038,z3,z4,z8]),(0,[z1,z2,z1039,z3,z4,z8])],[(0,[z422,z127,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z1040,z6]),(0,[z17,z2,z3,z4,z5,z16]),(0,[z1,z2,z753,z3,z4,z161]),(0,[z1,z3,z4,z8,z16,z334])],[],[(0,[z1,z2,z3,z186,z8,z320]),(0,[z1,z2,z3,z186,z8,z321]),(0,[z1,z2,z3,z4,z1041,z6]),(0,[z1,z2,z3,z4,z22,z281]),(0,[z1,z2,z9,z10,z8,z47])]],
   [[(0,[z1,z2,z1042,z3,z4,z443]),(0,[z1,z2,z3,z4,z8,z1043]),(0,[z1,z301,z467,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z1044]),(0,[z1,z3,z4,z8,z1045,z193])],[],[(0,[z1,z2,z1046,z3,z4,z8])],[(0,[z1,z2,z3,z4,z248,z320]),(0,[z1,z2,z3,z4,z248,z321]),(0,[z1,z118,z3,z4,z22,z180])],[(0,[z1,z2,z3,z1047,z4,z6]),(0,[z18,z1,z736,z4,z8,z6]),(0,[z1,z2,z753,z3,z4,z6]),(0,[z1,z2,z1048,z3,z4,z8]),(0,[z1,z2,z4,z8,z819,z6]),(0,[z1,z219,z3,z4,z8,z1049]),(0,[z98,z2,z262,z3,z4,z8])],[(0,[z1,z2,z3,z86,z4,z8]),(0,[z1,z2,z3,z4,z8,z1050]),(0,[z1,z2,z41,z4,z8,z879])],[(0,[z1,z2,z116,z3,z46,z6])],[(0,[z1,z2,z3,z4,z914,z248]),(0,[z1,z2,z3,z4,z8,z1051]),(0,[z1,z2,z287,z3,z4,z46]),(0,[z1,z2,z799,z4,z8,z47])],[(0,[z1,z2,z3,z4,z8,z1052])],[(0,[z1,z2,z1053,z3,z4,z8]),(0,[z1,z3,z4,z8,z474,z16]),(0,[z18,z392,z27,z4,z8,z6])],[(0,[z1,z2,z1054,z3,z4,z6]),(0,[z1,z2,z3,z4,z8,z1055])],[(0,[z1,z2,z3,z4,z1056,z6]),(0,[z1,z2,z3,z4,z8,z1057])],[(0,[z1,z1058,z3,z4,z8,z6]),(0,[z1,z148,z3,z4,z52,z6]),(0,[z78,z2,z400,z3,z15,z8]),(0,[z138,z1,z2,z43,z3,z6]),(0,[z18,z1,z2,z4,z8,z300])],[(0,[z1,z2,z3,z4,z8,z1059]),(0,[z18,z1,z27,z4,z8,z6]),(0,[z288,z2,z1060,z4,z8,z6])],[(0,[z1,z2,z3,z4,z22,z483]),(0,[z1,z59,z3,z275,z8,z266]),(0,[z1,z2,z357,z4,z8,z16]),(0,[z1061,z2,z3,z4,z8,z6]),(0,[z1,z2,z287,z40,z3,z4])],[(0,[z1,z2,z3,z4,z1062,z6]),(0,[z1,z2,z4,z8,z70,z161])]],
   [[(0,[z1,z219,z85,z4,z8,z6]),(1,[z17,z2,z116,z3,z6]),(0,[z1,z2,z301,z3,z4,z195]),(0,[z1,z2,z1063,z3,z4,z8]),(0,[z1,z2,z309,z287,z3,z4])],[(0,[z2,z3,z4,z64,z443,z6]),(0,[z1,z2,z3,z4,z52,z169]),(0,[z1,z2,z11,z458,z4,z8]),(0,[z1,z2,z1018,z4,z8,z16]),(0,[z1,z2,z61,z99,z22,z8]),(0,[z1,z2,z3,z4,z19,z154])],[(0,[z1,z2,z1064,z3,z8,z6]),(0,[z1,z3,z4,z8,z47,z657])],[(0,[z1,z148,z3,z4,z8,z6]),(0,[z2,z3,z4,z64,z685,z6]),(0,[z2,z3,z4,z8,z838,z6]),(0,[z1065,z2,z3,z4,z8,z6]),(0,[z1,z2,z1066,z3,z4,z8]),(0,[z31,z1,z3,z4,z94,z8])],[(0,[z1,z2,z1067,z3,z4,z52]),(0,[z1,z2,z3,z1068,z4,z8]),(0,[z652,z2,z3,z4,z8,z128]),(0,[z1,z2,z48,z4,z819,z6])],[(0,[z1,z2,z929,z4,z8,z6]),(0,[z1,z2,z3,z4,z1069,z8]),(0,[z0,z2,z3,z4,z22,z64]),(0,[z42,z1,z3,z4,z8,z47]),(0,[z1,z2,z3,z4,z8,z1070])],[(0,[z1,z2,z3,z4,z52,z6]),(0,[z1,z2,z3,z4,z8,z161]),(0,[z1,z2,z3,z4,z8,z1071]),(0,[z1,z2,z891,z3,z4,z8])],[(0,[z1,z2,z287,z3,z4,z216]),(0,[z1,z2,z3,z4,z1072,z8])],[(0,[z1,z2,z1073,z247,z4,z8]),(0,[z1,z59,z11,z3,z275,z8]),(0,[z1,z2,z287,z249,z3,z4]),(0,[z1,z2,z3,z4,z1074,z6])],[(0,[z1,z1075,z3,z4,z8,z6]),(0,[z1,z1076,z3,z4,z8,z6]),(0,[z1,z2,z1077,z4,z8,z6])],[(0,[z1,z2,z11,z184,z4,z8]),(0,[z1,z2,z555,z4,z8,z524]),(0,[z1,z2,z359,z4,z302,z8])],[(0,[z1,z2,z3,z4,z8,z1078]),(0,[z1079,z2,z3,z4,z8,z6]),(0,[z1,z82,z3,z4,z8,z47])],[(0,[z1,z144,z3,z843,z8,z6]),(0,[z1,z219,z2,z11,z3,z4])],[(0,[z1,z2,z3,z4,z8,z6]),(1,[z2,z3,z827,z8,z6]),(0,[z1,z59,z3,z275,z8,z16]),(0,[z199,z1,z3,z4,z94,z8]),(0,[z1,z2,z1080,z3,z4,z8])],[(0,[z1,z2,z3,z1081,z8,z6]),(0,[z1,z2,z1073,z3,z4,z8]),(0,[z1,z2,z11,z3,z186,z8])],[(0,[z217,z2,z156,z4,z8,z6]),(0,[z1,z2,z1082,z4,z8,z6]),(0,[z1,z2,z315,z287,z3,z4]),(0,[z1,z2,z1083,z4,z22,z8])]],
   [[(0,[z570,z2,z3,z4,z8,z75]),(0,[z1,z2,z4,z8,z70,z879])],[(0,[z1,z26,z87,z4,z8,z192]),(0,[z1,z2,z3,z4,z8,z1084]),(0,[z2,z3,z4,z8,z211,z47]),(0,[z1,z2,z3,z4,z8,z1085])],[(0,[z1,z398,z3,z4,z8,z960]),(0,[z1,z2,z324,z11,z3,z4]),(0,[z1,z3,z4,z8,z715,z16])],[(0,[z1,z149,z411,z4,z60,z6]),(0,[z1,z2,z3,z4,z203,z6]),(0,[z1,z2,z3,z4,z1086,z8]),(0,[z1,z2,z1087,z4,z8,z6]),(0,[z1,z2,z95,z4,z8,z504])],[(0,[z1,z2,z1088,z3,z4,z8]),(0,[z1,z2,z1089,z3,z4,z8])],[(0,[z1,z2,z3,z4,z1090,z6]),(0,[z1,z2,z3,z4,z8,z1091])],[(0,[z1,z2,z3,z4,z8,z1092]),(0,[z1,z2,z3,z4,z8,z1093]),(0,[z1,z2,z3,z110,z111,z6]),(0,[z1,z2,z3,z4,z1094,z6]),(0,[z1,z2,z3,z4,z8,z1095])],[(0,[z18,z1,z82,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1096]),(0,[z1,z2,z3,z4,z22,z612]),(0,[z1,z2,z3,z4,z8,z1097]),(0,[z1,z2,z3,z4,z8,z1098]),(0,[z1,z2,z3,z4,z8,z879]),(0,[z1,z2,z3,z4,z8,z729])],[(0,[z1,z2,z3,z4,z8,z226]),(0,[z1,z2,z1099,z3,z4,z8])],[(0,[z1,z2,z4,z19,z111,z6]),(0,[z1,z2,z3,z4,z1100,z6]),(0,[z1,z4,z8,z255,z47,z16]),(0,[z1101,z2,z3,z4,z8,z6])],[(0,[z1,z2,z1102,z3,z8,z6]),(0,[z78,z17,z2,z315,z3,z6]),(0,[z1,z2,z41,z4,z8,z320]),(0,[z1,z2,z1103,z3,z4,z8])],[(0,[z223,z2,z156,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1104]),(0,[z1,z2,z1105,z3,z4,z8])],[(0,[z1,z2,z3,z4,z8,z1106])],[(0,[z1,z2,z3,z119,z532,z6]),(0,[z1,z2,z3,z4,z8,z1107]),(0,[z1,z3,z4,z943,z8,z6]),(0,[z1,z2,z29,z3,z4,z8])],[],[(0,[z1,z2,z377,z4,z22,z8]),(0,[z1,z2,z3,z4,z1108,z52]),(0,[z1,z2,z3,z4,z8,z1109]),(0,[z38,z2,z3,z4,z8,z105]),(0,[z1,z2,z1110,z3,z4,z8]),(0,[z1,z2,z3,z8,z6,z735])]],
   [[(0,[z1,z397,z149,z11,z3,z4])],[(0,[z2,z3,z4,z8,z103,z211])],[(0,[z1,z2,z3,z4,z8,z1111]),(0,[z1,z584,z3,z4,z8,z16]),(0,[z1,z219,z11,z3,z4,z6])],[(0,[z1,z2,z3,z4,z8,z1112]),(0,[z38,z1,z2,z106,z4,z8]),(0,[z288,z2,z315,z3,z46,z6])],[(0,[z1,z2,z1113,z3,z4,z8]),(0,[z78,z2,z3,z15,z443,z6]),(0,[z1,z2,z1114,z3,z4,z8])],[(0,[z1,z398,z11,z3,z4,z8]),(0,[z536,z1,z3,z4,z8,z47]),(0,[z18,z1,z27,z4,z8,z16]),(0,[z1,z2,z969,z4,z8,z6])],[(0,[z1,z2,z10,z110,z8,z6])],[(0,[z1,z2,z106,z4,z8,z6]),(0,[z1,z2,z11,z9,z10,z8])],[(0,[z1,z2,z505,z3,z4,z22]),(0,[z1,z2,z4,z19,z819,z6]),(0,[z1,z2,z11,z3,z4,z650]),(0,[z2,z3,z4,z8,z6,z1115])],[(0,[z1,z2,z51,z4,z8,z206]),(0,[z223,z2,z3,z110,z8,z6])],[(0,[z1,z2,z3,z4,z1116,z161]),(0,[z288,z2,z3,z4,z8,z47])],[(0,[z1,z148,z3,z4,z8,z16]),(0,[z17,z2,z218,z3,z4,z5]),(0,[z1,z522,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z1117]),(0,[z1,z2,z11,z3,z4,z511]),(0,[z1,z2,z287,z3,z4,z81]),(0,[z1,z2,z3,z4,z8,z1118])],[(0,[z78,z398,z3,z15,z8,z6]),(0,[z18,z1,z27,z4,z8,z320]),(0,[z18,z1,z27,z4,z8,z321]),(0,[z1,z2,z3,z4,z8,z1119]),(0,[z1,z1120,z3,z4,z8,z6])],[(0,[z1,z2,z3,z1121,z8,z6]),(0,[z1,z2,z11,z377,z4,z8]),(0,[z1,z2,z1122,z3,z4,z8]),(0,[z1,z2,z11,z3,z4,z111]),(0,[z1,z2,z11,z3,z4,z248]),(0,[z1,z2,z287,z3,z4,z6]),(0,[z1,z2,z106,z4,z203,z6]),(0,[z235,z2,z3,z4,z449,z8])],[(0,[z1,z1123,z3,z4,z8,z6]),(0,[z1,z148,z184,z4,z8,z6]),(0,[z1,z2,z3,z81,z443,z6]),(0,[z1,z2,z3,z4,z52,z16]),(0,[z1,z2,z3,z8,z6,z1124]),(0,[z1,z2,z3,z4,z987,z111]),(0,[z1,z1125,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z175]),(0,[z1,z2,z1126,z3,z4,z8]),(0,[z1,z2,z11,z464,z4,z19])]],
   [[(0,[z1,z2,z3,z1127,z8,z6]),(0,[z1,z2,z43,z3,z4,z22]),(0,[z0,z2,z3,z4,z64,z6]),(0,[z1,z2,z1128,z4,z8,z6]),(0,[z1,z2,z3,z4,z943,z6]),(0,[z1,z2,z11,z3,z4,z69])],[(0,[z1,z2,z184,z4,z52,z6]),(0,[z78,z2,z3,z827,z8,z6]),(0,[z2,z116,z3,z64,z8,z6]),(0,[z1,z2,z3,z4,z1116,z6]),(0,[z1,z144,z3,z21,z8,z16]),(0,[z1,z118,z2,z287,z3,z4]),(0,[z1,z2,z3,z4,z8,z1129]),(0,[z1,z2,z11,z3,z4,z692])],[(0,[z1,z2,z543,z10,z8,z6]),(0,[z1,z2,z464,z4,z19,z6])],[(0,[z1,z2,z3,z4,z1130,z6]),(0,[z1,z1131,z3,z4,z8,z6]),(0,[z1,z2,z1067,z3,z4,z8]),(0,[z1,z2,z3,z4,z1132,z8]),(0,[z1,z2,z411,z4,z19,z6]),(0,[z1,z2,z11,z3,z119,z81])],[(0,[z1,z2,z3,z4,z8,z1133]),(1,[z1,z2,z753,z3,z4]),(0,[z1,z2,z411,z4,z22,z8]),(0,[z1134,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z1135,z4,z8]),(0,[z1,z2,z3,z4,z8,z1136]),(0,[z1,z2,z4,z8,z70,z320]),(0,[z1,z2,z3,z4,z8,z1137]),(0,[z1,z2,z3,z4,z16,z1032]),(1,[z1,z2,z4,z819,z6])],[(0,[z1,z2,z3,z4,z1138,z8]),(0,[z1,z2,z287,z3,z147,z4]),(0,[z1,z2,z287,z3,z4,z60])],[(0,[z1,z2,z287,z87,z3,z4])],[(0,[z1,z2,z184,z4,z8,z6]),(0,[z1,z2,z3,z4,z1139,z8]),(0,[z1,z2,z3,z556,z81,z6]),(0,[z1,z2,z48,z4,z111,z6]),(0,[z1,z411,z4,z180,z8,z6]),(0,[z1,z2,z4,z316,z8,z47]),(0,[z1,z2,z3,z4,z6,z729])],[(0,[z1,z2,z51,z4,z8,z47]),(0,[z1,z2,z1140,z4,z8,z6]),(0,[z1,z2,z3,z4,z719,z108]),(0,[z1,z2,z3,z442,z468,z8])],[(0,[z1,z2,z3,z4,z8,z1141]),(0,[z1,z2,z3,z97,z4,z16]),(0,[z1,z609,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z1142]),(0,[z1,z2,z3,z4,z94,z8]),(0,[z1,z118,z3,z4,z180,z145]),(0,[z1,z3,z4,z94,z8,z16])],[(0,[z1,z2,z3,z4,z203,z16]),(0,[z1,z2,z740,z11,z4,z8])],[(0,[z1,z2,z1143,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z320]),(0,[z1,z2,z3,z4,z8,z321]),(0,[z1,z2,z11,z3,z4,z115])],[(0,[z1,z2,z3,z4,z8,z1144]),(0,[z1,z3,z4,z180,z621,z6]),(0,[z1,z2,z315,z3,z22,z46])],[(0,[z1,z2,z3,z4,z1145,z6]),(0,[z1,z2,z11,z3,z312,z4]),(0,[z1,z219,z48,z4,z108,z6])],[(0,[z1,z3,z21,z843,z8,z6]),(0,[z1,z159,z2,z287,z3,z4]),(0,[z1,z2,z3,z4,z92,z6]),(0,[z2,z3,z4,z8,z1146,z6])]],
   [[(0,[z1,z2,z3,z4,z8,z1147]),(0,[z1,z2,z3,z186,z111,z6]),(0,[z1,z2,z3,z1148,z8,z6]),(0,[z1,z26,z87,z4,z8,z47]),(0,[z1,z2,z3,z4,z1149,z8]),(0,[z1,z3,z4,z8,z278,z47]),(0,[z1,z2,z3,z4,z8,z121])],[(0,[z1,z148,z3,z4,z8,z169]),(0,[z1,z2,z3,z4,z6,z1150]),(0,[z1,z2,z3,z4,z1151,z6]),(0,[z1,z2,z3,z4,z8,z1152]),(0,[z1153,z1,z2,z287,z3,z4])],[(0,[z1,z2,z156,z4,z8,z47]),(0,[z1,z2,z3,z4,z8,z1154]),(0,[z1,z526,z2,z11,z3,z4]),(0,[z1,z2,z3,z4,z8,z1155])],[(0,[z595,z1,z2,z11,z3,z4])],[(0,[z1,z2,z1156,z3,z4,z8]),(0,[z1,z2,z9,z342,z8,z6]),(0,[z1,z398,z3,z4,z22,z8]),(0,[z1,z2,z758,z43,z3,z4]),(0,[z18,z1,z4,z19,z180,z6]),(0,[z1,z2,z3,z4,z8,z1157])],[(0,[z1,z2,z3,z4,z8,z1158]),(0,[z138,z2,z3,z63,z8,z47]),(0,[z1,z1159,z3,z4,z8,z6])],[(0,[z1,z2,z1160,z3,z4,z6]),(0,[z1,z2,z3,z4,z8,z1161]),(0,[z1,z159,z467,z3,z4,z8]),(0,[z1,z2,z11,z1162,z4,z8])],[(0,[z1,z607,z3,z275,z8,z6]),(0,[z1,z2,z3,z1163,z8,z6]),(0,[z1,z2,z3,z4,z8,z1164])],[(0,[z1,z2,z3,z4,z201,z203]),(0,[z1,z2,z921,z3,z4,z8])],[(0,[z1,z2,z3,z4,z1165,z6]),(0,[z146,z1,z2,z106,z4,z8]),(0,[z1166,z1,z2,z287,z3,z4])],[(0,[z130,z83,z3,z4,z8,z6]),(0,[z1,z1167,z3,z4,z8,z6]),(0,[z1,z2,z1162,z4,z8,z6]),(0,[z1,z2,z3,z4,z1168,z6]),(0,[z1,z2,z3,z4,z8,z1169]),(0,[z1,z2,z11,z3,z4,z177]),(0,[z1,z2,z3,z4,z8,z1170]),(0,[z2,z3,z4,z8,z1171,z6])],[(0,[z1,z2,z3,z4,z8,z169]),(0,[z1,z2,z3,z97,z4,z1161]),(0,[z1,z2,z11,z3,z4,z195])],[(0,[z1,z2,z247,z4,z22,z8]),(0,[z392,z2,z3,z110,z8,z6]),(0,[z1,z2,z3,z4,z22,z111]),(0,[z1,z2,z3,z4,z22,z248]),(0,[z1,z144,z3,z21,z8,z6])],[(0,[z1,z2,z3,z4,z8,z1172]),(0,[z1,z2,z3,z4,z1173,z6]),(0,[z1,z2,z3,z4,z1174,z8]),(0,[z1,z2,z3,z4,z8,z1175]),(0,[z1,z2,z150,z4,z8,z47]),(0,[z31,z1,z2,z11,z3,z4])],[(0,[z1,z2,z3,z1176,z8,z6]),(0,[z1,z2,z3,z4,z1108,z8]),(0,[z1,z2,z755,z99,z8,z6]),(0,[z1,z2,z3,z4,z8,z1177]),(0,[z1,z2,z315,z239,z3,z46])],[(0,[z1,z2,z3,z4,z8,z1178]),(0,[z1,z2,z11,z3,z4,z482]),(0,[z18,z1,z324,z4,z8,z6]),(0,[z1179,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z1180,z8]),(1,[z1,z2,z287,z3,z4]),(0,[z1,z2,z106,z4,z8,z16]),(0,[z1,z2,z3,z7,z8,z622])]],
   [[(0,[z17,z2,z3,z4,z554,z5]),(0,[z1,z2,z3,z110,z8,z47]),(0,[z1,z2,z11,z682,z3,z4]),(0,[z1,z2,z4,z8,z6,z1181])],[(0,[z1,z2,z3,z4,z8,z838]),(0,[z38,z2,z3,z558,z4,z8]),(0,[z1,z2,z3,z4,z1182,z6]),(0,[z1,z2,z4,z8,z1183,z6]),(0,[z1,z2,z3,z8,z735,z93])],[(0,[z1,z2,z3,z4,z8,z1184]),(0,[z1,z2,z4,z8,z1185,z6]),(0,[z1,z2,z315,z3,z103,z46])],[(0,[z1,z2,z41,z53,z4,z8]),(0,[z223,z2,z3,z186,z8,z6]),(0,[z1,z2,z1186,z3,z4,z8])],[(0,[z1,z2,z794,z4,z22,z8])],[(0,[z1,z2,z3,z4,z8,z1187]),(0,[z1,z2,z3,z4,z1188,z8]),(0,[z1,z2,z3,z97,z4,z6]),(0,[z392,z2,z3,z4,z22,z8]),(0,[z1,z2,z287,z3,z4,z16]),(0,[z1,z2,z106,z4,z203,z16]),(0,[z1,z2,z61,z11,z99,z8])],[(0,[z223,z2,z11,z3,z4,z8]),(0,[z1,z2,z106,z4,z8,z320]),(0,[z1,z2,z3,z4,z1189,z8])],[(0,[z1,z2,z3,z1190,z8,z6]),(0,[z223,z2,z3,z4,z248,z6])],[(0,[z0,z2,z3,z4,z64,z16]),(0,[z1,z219,z3,z4,z111,z6]),(0,[z1,z2,z1191,z3,z4,z8]),(0,[z1,z11,z3,z4,z193,z108])],[(0,[z1,z2,z1192,z3,z4,z8]),(0,[z1,z2,z11,z4,z19,z108])],[(0,[z1,z2,z3,z4,z8,z1193]),(0,[z1,z2,z3,z4,z1194,z8])],[(0,[z1,z2,z1195,z3,z4,z8]),(0,[z1,z2,z4,z459,z316,z8])],[(0,[z1,z2,z3,z4,z8,z1196]),(0,[z1,z2,z106,z287,z4,z8]),(0,[z1,z2,z3,z4,z22,z92])],[(0,[z1,z2,z1197,z4,z8,z6]),(0,[z1,z2,z991,z3,z4,z8]),(0,[z1,z2,z4,z8,z255,z161]),(0,[z1,z2,z287,z3,z4,z91])],[(0,[z1,z688,z3,z4,z8,z16]),(0,[z288,z1,z2,z315,z3,z6])],[(0,[z1,z2,z3,z4,z8,z1198]),(0,[z1,z2,z736,z4,z8,z6]),(0,[z1,z219,z3,z4,z60,z6])]],
   [[(0,[z1,z2,z184,z4,z8,z16]),(0,[z1,z2,z1199,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1200]),(0,[z1,z2,z48,z4,z22,z108]),(0,[z288,z2,z239,z3,z4,z8])],[(0,[z1201,z2,z3,z4,z8,z6]),(0,[z1,z2,z48,z287,z3,z4]),(0,[z1,z2,z11,z3,z4,z729])],[(0,[z1,z2,z3,z1202,z8,z6]),(0,[z1,z2,z3,z1203,z4,z8]),(0,[z1,z219,z3,z4,z91,z6]),(0,[z1,z2,z3,z4,z22,z356])],[(0,[z427,z2,z147,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1204]),(0,[z98,z2,z3,z4,z8,z75])],[(0,[z1,z2,z315,z3,z443,z6]),(0,[z1,z2,z4,z8,z255,z6]),(0,[z1,z2,z354,z3,z197,z8])],[(0,[z1,z2,z3,z4,z8,z1205]),(0,[z1,z2,z1206,z3,z4,z8]),(0,[z1207,z2,z3,z4,z8,z6])],[(0,[z1,z591,z3,z4,z8,z16])],[(0,[z1,z2,z3,z4,z92,z16]),(0,[z1,z2,z88,z287,z3,z4]),(0,[z1,z2,z3,z79,z8,z164])],[(0,[z1,z398,z3,z4,z52,z6]),(0,[z1,z2,z3,z207,z8,z47]),(0,[z1,z2,z4,z8,z47,z900]),(0,[z1,z2,z41,z4,z8,z684]),(0,[z1,z2,z3,z81,z764,z6])],[(0,[z1,z2,z3,z4,z1004,z8]),(0,[z1,z2,z3,z4,z8,z266]),(0,[z1,z2,z3,z4,z1208,z8]),(0,[z1,z2,z3,z4,z8,z1209])],[(0,[z1,z2,z3,z4,z8,z1210]),(1,[z1,z149,z467,z3,z4]),(0,[z1,z2,z40,z4,z19,z409])],[(0,[z1,z2,z1211,z4,z8,z6]),(0,[z1,z2,z400,z3,z97,z4]),(0,[z1,z2,z3,z4,z1212,z8]),(0,[z1,z2,z40,z4,z19,z6])],[(0,[z1,z2,z3,z4,z8,z151]),(0,[z1,z2,z287,z3,z79,z4]),(0,[z1,z2,z3,z4,z8,z1049])],[(0,[z665,z2,z147,z4,z8,z6]),(0,[z1,z3,z4,z8,z193,z6]),(0,[z1,z2,z4,z201,z8,z255]),(0,[z1,z2,z11,z3,z4,z302])],[(0,[z1,z2,z3,z4,z8,z1213]),(0,[z1,z2,z55,z4,z8,z879]),(0,[z1,z2,z55,z4,z8,z504])],[(0,[z1,z2,z1214,z4,z8,z6]),(0,[z0,z2,z3,z4,z793,z6]),(0,[z1,z2,z11,z3,z4,z621]),(0,[z1,z2,z3,z4,z8,z1215]),(0,[z1,z2,z61,z99,z8,z6]),(0,[z1,z2,z3,z4,z271,z6])]],
   [[(0,[z1,z2,z1216,z3,z4,z8]),(0,[z1,z59,z3,z843,z8,z6])],[(0,[z251,z2,z147,z4,z8,z47]),(0,[z1,z2,z11,z51,z4,z8]),(0,[z1,z2,z11,z3,z4,z697]),(0,[z1,z584,z2,z11,z3,z4])],[(0,[z130,z83,z3,z4,z8,z16]),(0,[z1,z2,z1217,z4,z8,z6]),(0,[z17,z2,z247,z4,z5,z6]),(0,[z1,z2,z287,z3,z27,z4]),(0,[z1,z2,z3,z4,z1168,z16])],[(0,[z1,z2,z3,z4,z8,z1218])],[(0,[z78,z2,z3,z15,z8,z206]),(0,[z1,z2,z11,z3,z4,z216])],[(0,[z1,z2,z3,z4,z8,z1219]),(0,[z223,z2,z3,z4,z22,z8]),(1,[z1,z2,z755,z8,z6])],[(0,[z1,z2,z184,z4,z8,z169]),(0,[z1,z2,z3,z4,z8,z1220]),(0,[z17,z2,z116,z3,z8,z6]),(0,[z392,z2,z3,z186,z8,z6]),(0,[z1,z2,z1221,z3,z4,z8])],[(0,[z1,z2,z150,z11,z4,z8]),(0,[z1,z2,z3,z4,z8,z1222]),(0,[z1179,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z195,z91]),(0,[z1,z2,z3,z4,z8,z1223])],[(0,[z1,z2,z3,z1224,z8,z6])],[(0,[z1,z2,z3,z4,z1225,z6]),(0,[z392,z2,z11,z3,z4,z8]),(0,[z1,z2,z3,z4,z1182,z16]),(0,[z2,z239,z3,z4,z8,z211])],[(0,[z392,z2,z3,z4,z248,z6]),(0,[z1,z2,z3,z186,z8,z47]),(0,[z1,z149,z11,z467,z3,z4]),(0,[z1,z3,z4,z8,z47,z715])],[(0,[z1,z2,z11,z3,z4,z510]),(0,[z1,z2,z3,z4,z8,z1226]),(0,[z1,z149,z3,z4,z60,z47])],[(0,[z1,z2,z3,z4,z8,z1227]),(0,[z1,z149,z2,z287,z3,z4]),(0,[z1,z2,z3,z4,z8,z719])],[(0,[z1,z26,z2,z58,z4,z8]),(0,[z1,z2,z1083,z4,z8,z6]),(0,[z1,z2,z3,z79,z8,z172])],[(0,[z17,z1,z2,z116,z3,z6]),(0,[z1,z2,z3,z4,z8,z1228]),(0,[z1,z2,z3,z4,z248,z47]),(0,[z1,z2,z3,z119,z81,z415])],[(0,[z17,z2,z3,z4,z5,z47]),(0,[z1,z2,z3,z4,z8,z1229]),(0,[z1,z2,z1230,z4,z8,z6]),(0,[z1,z2,z287,z3,z4,z124])]],
   [[(0,[z1,z2,z11,z3,z4,z92]),(0,[z1,z2,z3,z4,z22,z729])],[(0,[z1,z2,z3,z4,z8,z1231])],[(0,[z1,z2,z3,z4,z8,z1232]),(0,[z1,z3,z4,z180,z111,z6])],[(0,[z1,z149,z467,z3,z4,z8]),(0,[z1,z2,z304,z3,z8,z164])],[(0,[z78,z2,z3,z15,z8,z47]),(0,[z1,z2,z4,z8,z47,z945]),(0,[z1,z2,z11,z742,z4,z8])],[(0,[z1,z2,z3,z4,z1233,z8]),(0,[z1,z548,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z145])],[(0,[z1,z2,z1017,z377,z4,z8]),(0,[z1,z2,z400,z3,z4,z8]),(0,[z235,z2,z3,z4,z8,z128])],[(1,[z288,z2,z315,z3,z6])],[],[(0,[z1,z2,z1234,z4,z8,z6]),(0,[z1,z2,z287,z3,z4,z15])],[(0,[z1,z2,z3,z4,z91,z177])],[(0,[z1,z2,z1235,z4,z8,z6]),(0,[z1,z2,z1042,z3,z4,z8]),(0,[z1,z2,z3,z4,z203,z145]),(0,[z1,z48,z4,z193,z108,z6])],[(0,[z38,z2,z3,z4,z8,z75]),(0,[z1,z2,z3,z4,z1236,z6]),(0,[z1,z118,z3,z4,z943,z6]),(0,[z1,z2,z4,z8,z255,z16]),(0,[z1,z2,z3,z4,z8,z1237]),(0,[z1,z2,z3,z4,z8,z1238])],[(0,[z1,z2,z377,z4,z8,z6]),(0,[z84,z127,z156,z4,z8,z6]),(0,[z78,z2,z43,z3,z4,z6])],[(0,[z1,z2,z43,z3,z86,z4]),(0,[z1,z2,z3,z22,z207,z8]),(0,[z1,z2,z301,z3,z4,z108]),(0,[z1,z2,z3,z4,z302,z92])],[(0,[z1,z2,z1239,z3,z4,z6]),(0,[z1,z2,z3,z4,z443,z16]),(0,[z1,z2,z116,z3,z22,z8]),(0,[z0,z2,z3,z4,z64,z151]),(0,[z1,z118,z2,z467,z3,z4])]],
   [[(0,[z18,z1,z2,z58,z4,z8]),(0,[z78,z2,z43,z3,z15,z6]),(0,[z1,z2,z357,z4,z8,z47])],[(0,[z1,z1240,z3,z4,z8,z6]),(0,[z217,z2,z85,z4,z22,z8]),(0,[z1,z2,z1241,z3,z4,z8]),(0,[z1,z2,z1242,z3,z4,z8]),(0,[z1,z285,z3,z4,z8,z193])],[(0,[z18,z1,z546,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1243]),(0,[z1,z219,z3,z4,z8,z47]),(0,[z1,z2,z384,z3,z4,z22]),(0,[z1,z2,z708,z4,z22,z8])],[(0,[z1,z26,z4,z273,z8,z6]),(0,[z1,z2,z1244,z3,z4,z8]),(0,[z1,z2,z3,z4,z195,z60]),(0,[z1,z2,z40,z4,z19,z16])],[(0,[z1,z2,z3,z4,z8,z1245]),(0,[z1,z3,z4,z94,z180,z8]),(0,[z1,z2,z4,z22,z8,z739])],[(0,[z2,z3,z63,z827,z8,z6]),(0,[z0,z2,z3,z4,z64,z175]),(0,[z1,z2,z11,z3,z705,z4]),(0,[z1,z3,z4,z8,z193,z16])],[(0,[z1,z2,z3,z4,z8,z1246]),(0,[z1,z2,z3,z1247,z4,z8]),(0,[z1,z2,z11,z3,z4,z552]),(0,[z1,z2,z3,z4,z8,z1248])],[(0,[z1,z2,z1249,z3,z4,z8]),(0,[z1,z2,z61,z99,z8,z16]),(0,[z1,z2,z3,z4,z271,z16]),(0,[z288,z2,z315,z3,z4,z6])],[(0,[z1,z2,z309,z3,z8,z93]),(0,[z1,z2,z3,z4,z8,z1250])],[(0,[z1,z2,z3,z4,z8,z1251]),(0,[z318,z2,z3,z4,z8,z129])],[(1,[z824,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1252]),(0,[z1,z2,z495,z99,z8,z6]),(0,[z1,z2,z301,z3,z4,z19]),(0,[z1,z2,z1060,z4,z8,z6])],[(0,[z1,z2,z1253,z3,z8,z6]),(0,[z1,z2,z116,z218,z3,z8]),(0,[z1,z2,z3,z843,z8,z6]),(0,[z1,z2,z3,z4,z6,z1254]),(0,[z1,z1255,z11,z3,z4,z8])],[(0,[z78,z2,z3,z81,z64,z6]),(0,[z0,z2,z3,z579,z4,z6]),(0,[z1,z2,z3,z4,z1256,z6]),(0,[z1,z2,z3,z4,z8,z284]),(0,[z1,z2,z3,z4,z819,z6]),(0,[z288,z2,z789,z4,z8,z6])],[(0,[z1,z2,z1257,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z1258]),(0,[z1,z118,z149,z11,z3,z4]),(0,[z1,z2,z3,z4,z8,z1259])],[(0,[z251,z2,z58,z147,z4,z8]),(0,[z1,z2,z315,z3,z764,z6])],[(0,[z1,z2,z1260,z3,z4,z6]),(0,[z1,z59,z3,z275,z8,z47]),(0,[z1,z159,z3,z4,z8,z16])]],
   [[(0,[z1,z2,z287,z85,z3,z4]),(0,[z1,z148,z3,z4,z443,z6]),(0,[z1,z2,z458,z4,z22,z8]),(0,[z1,z2,z3,z1261,z8,z6])],[(0,[z1,z3,z4,z843,z8,z6]),(0,[z1,z118,z2,z29,z3,z4]),(0,[z1,z2,z3,z4,z91,z729])],[(0,[z1,z2,z3,z4,z8,z257]),(0,[z1,z2,z411,z4,z8,z6]),(0,[z1,z2,z4,z8,z16,z1181])],[(0,[z1,z2,z55,z352,z4,z8]),(0,[z1,z2,z3,z4,z8,z1262])],[(0,[z1,z2,z850,z4,z8,z6]),(0,[z84,z127,z3,z4,z22,z8]),(0,[z1,z2,z43,z11,z3,z4]),(0,[z1,z2,z3,z1263,z8,z6]),(0,[z1,z219,z11,z3,z4,z108]),(0,[z1,z2,z11,z3,z4,z504])],[(0,[z84,z127,z3,z4,z8,z49]),(0,[z1,z2,z776,z4,z8,z6]),(0,[z1,z2,z3,z4,z443,z169]),(0,[z1,z159,z3,z4,z203,z16])],[(0,[z2,z43,z3,z63,z4,z6]),(0,[z1,z2,z3,z4,z8,z1264]),(0,[z1,z2,z1087,z467,z4,z8]),(0,[z1,z2,z3,z4,z22,z91])],[(0,[z146,z2,z3,z4,z8,z337])],[],[(0,[z17,z2,z336,z3,z4,z6])],[(0,[z1,z2,z1265,z3,z4,z8]),(0,[z1,z2,z3,z4,z443,z6]),(0,[z1,z144,z3,z21,z8,z395]),(1,[z1,z3,z4,z943,z6]),(0,[z1,z219,z3,z4,z8,z153])],[(0,[z1,z2,z3,z4,z22,z498]),(0,[z1,z2,z3,z4,z1266,z6]),(0,[z1,z2,z861,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z1267]),(0,[z1,z2,z1268,z3,z4,z8])],[(0,[z1,z2,z3,z1269,z8,z6]),(0,[z1,z2,z3,z4,z8,z1270]),(0,[z1,z398,z3,z4,z8,z169]),(0,[z1,z2,z287,z3,z1271,z4])],[(0,[z1,z2,z43,z400,z3,z4]),(0,[z1,z2,z3,z4,z8,z395])],[(0,[z1,z398,z3,z4,z8,z1175]),(0,[z1,z2,z3,z4,z1272,z8]),(0,[z1,z26,z4,z8,z142,z6]),(0,[z1,z2,z287,z3,z4,z108])]],
   [[(0,[z1,z2,z3,z4,z52,z206]),(0,[z1,z2,z1273,z4,z8,z6])],[(0,[z1,z2,z1274,z3,z4,z8]),(0,[z2,z3,z827,z15,z8,z6]),(0,[z1,z2,z287,z3,z4,z105]),(0,[z1,z2,z3,z4,z1275,z6])],[(0,[z1,z398,z3,z4,z8,z6]),(0,[z1,z293,z3,z4,z8,z16]),(0,[z1,z2,z1276,z3,z4,z8])],[(0,[z1,z2,z9,z10,z8,z300]),(0,[z1,z2,z3,z4,z8,z154])],[(0,[z1,z2,z3,z4,z8,z1277]),(0,[z2,z3,z4,z8,z75,z838]),(0,[z1,z26,z2,z11,z4,z19])],[(0,[z1,z2,z377,z4,z8,z16]),(0,[z17,z2,z116,z3,z5,z6]),(0,[z1,z2,z3,z4,z8,z1278]),(0,[z2,z3,z4,z22,z8,z211])],[(0,[z78,z1,z2,z287,z3,z4]),(0,[z1,z2,z1279,z3,z4,z8]),(0,[z1,z2,z3,z4,z1280,z6]),(0,[z1,z2,z48,z4,z108,z6])],[(0,[z1,z2,z3,z4,z8,z1281]),(0,[z1,z2,z1239,z3,z4,z16])],[(0,[z1,z2,z218,z3,z4,z8]),(0,[z1,z87,z4,z8,z687,z6])],[(0,[z1,z159,z106,z4,z8,z16]),(0,[z288,z2,z3,z4,z8,z103])],[(0,[z1,z2,z247,z4,z8,z6]),(0,[z1,z2,z287,z3,z21,z4])],[(0,[z1,z2,z1282,z4,z8,z6]),(0,[z1,z2,z3,z4,z1283,z8]),(1,[z78,z2,z43,z3,z6]),(0,[z1,z2,z287,z3,z4,z19]),(0,[z1,z2,z11,z3,z4,z661])],[(0,[z1,z2,z3,z4,z8,z319]),(0,[z2,z3,z63,z8,z672,z6]),(0,[z17,z1,z2,z287,z3,z4]),(0,[z1,z2,z3,z4,z8,z1284]),(0,[z1,z2,z1285,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1286])],[(0,[z84,z1,z2,z287,z3,z4]),(0,[z1,z2,z150,z10,z8,z6]),(0,[z1,z3,z4,z203,z47,z16])],[(0,[z1,z2,z3,z4,z8,z1287]),(0,[z1,z2,z1288,z4,z8,z6]),(0,[z1,z2,z3,z827,z8,z6]),(0,[z1,z2,z1289,z4,z8,z6]),(0,[z1,z2,z3,z4,z1290,z8])],[(0,[z1,z2,z1291,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z1292]),(0,[z1,z118,z3,z4,z180,z47]),(0,[z1,z159,z287,z3,z4,z16]),(0,[z1,z2,z3,z4,z8,z1293]),(0,[z1,z2,z11,z3,z4,z35])]],
   [[(0,[z1,z2,z1294,z4,z8,z6]),(0,[z251,z1,z2,z287,z3,z4]),(0,[z1,z2,z3,z4,z52,z47]),(0,[z18,z1,z27,z4,z111,z6]),(0,[z1,z2,z3,z1295,z8,z6]),(0,[z1,z460,z2,z11,z3,z4])],[],[(0,[z1,z2,z3,z4,z8,z1296]),(0,[z1,z2,z794,z4,z8,z6]),(0,[z1,z2,z3,z4,z1074,z47]),(0,[z1,z2,z48,z4,z153,z108])],[(0,[z392,z2,z3,z4,z8,z6]),(0,[z1,z2,z11,z357,z4,z8]),(0,[z1,z2,z3,z4,z8,z1045])],[(0,[z74,z1,z2,z3,z4,z92]),(0,[z1,z2,z106,z4,z8,z93])],[(0,[z1,z2,z3,z4,z1297,z6]),(0,[z84,z824,z3,z4,z8,z6]),(0,[z1,z2,z11,z891,z3,z4]),(0,[z1,z2,z3,z4,z8,z1298]),(0,[z1,z2,z1299,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z1300]),(0,[z17,z2,z458,z4,z5,z6])],[(0,[z1,z2,z3,z4,z8,z47]),(0,[z1,z2,z1301,z3,z8,z6]),(0,[z74,z2,z3,z4,z8,z838]),(0,[z74,z2,z277,z3,z4,z8]),(0,[z18,z1,z2,z11,z4,z19]),(0,[z1,z3,z4,z201,z94,z8]),(0,[z1,z2,z9,z10,z22,z8])],[(0,[z84,z127,z11,z3,z4,z8]),(0,[z223,z2,z3,z4,z8,z16])],[(0,[z1,z2,z3,z4,z8,z1302]),(0,[z1303,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z201,z8]),(0,[z1,z2,z3,z4,z8,z1304]),(0,[z2,z11,z3,z4,z8,z211])],[(0,[z1,z2,z3,z4,z8,z1305]),(0,[z1,z2,z411,z4,z8,z16]),(0,[z1,z2,z287,z3,z4,z93])],[(0,[z1,z2,z218,z3,z207,z8])],[(0,[z1,z2,z3,z726,z8,z6]),(0,[z1,z2,z1306,z3,z4,z8])],[(0,[z223,z2,z147,z4,z8,z6]),(0,[z1,z2,z3,z1307,z4,z8]),(0,[z1,z2,z3,z4,z203,z47]),(0,[z1,z2,z3,z4,z92,z172])],[(0,[z1,z2,z3,z4,z8,z1308]),(0,[z1,z2,z1309,z3,z4,z8])],[(0,[z1,z2,z1310,z4,z8,z6]),(0,[z223,z2,z3,z4,z8,z321]),(0,[z1,z87,z736,z4,z8,z6]),(0,[z1,z3,z4,z8,z476,z47]),(0,[z253,z2,z3,z4,z295,z8])]],
   [[(0,[z1,z2,z3,z4,z8,z1311]),(0,[z1,z2,z3,z4,z111,z6]),(0,[z1,z2,z3,z4,z8,z1312]),(0,[z1,z2,z3,z4,z8,z1313])],[(0,[z1,z676,z2,z11,z3,z4]),(0,[z1,z2,z3,z1314,z8,z6]),(0,[z38,z1,z2,z287,z3,z4]),(0,[z1,z2,z3,z4,z8,z1315])],[(0,[z1,z2,z3,z4,z8,z1316])],[(0,[z1,z2,z1317,z287,z3,z4])],[(0,[z1,z2,z287,z3,z63,z4]),(0,[z1,z2,z287,z1318,z3,z4]),(0,[z1,z2,z1319,z3,z4,z8])],[(0,[z1,z2,z3,z4,z1320,z8]),(0,[z1,z2,z184,z4,z443,z6]),(0,[z1,z2,z3,z4,z8,z1321]),(0,[z1,z26,z87,z4,z22,z8]),(0,[z1,z2,z287,z3,z4,z203])],[(0,[z1,z1322,z3,z4,z8,z6]),(0,[z1,z3,z4,z8,z16,z270]),(0,[z1,z2,z9,z10,z8,z107]),(0,[z1,z2,z11,z40,z4,z19])],[(0,[z1,z2,z1323,z4,z8,z6]),(0,[z1,z2,z3,z4,z1324,z6]),(0,[z78,z2,z3,z189,z8,z6]),(0,[z1,z2,z11,z3,z110,z8]),(0,[z1,z149,z3,z4,z943,z6]),(0,[z1,z2,z41,z287,z3,z4]),(0,[z1,z2,z438,z3,z8,z487]),(0,[z1,z2,z11,z3,z4,z691])],[(0,[z74,z2,z645,z3,z4,z8]),(0,[z1,z2,z357,z4,z8,z730])],[(0,[z1,z2,z3,z4,z1325,z8]),(0,[z1,z2,z150,z110,z8,z6]),(0,[z1,z2,z11,z3,z4,z108]),(0,[z1,z2,z3,z4,z22,z634])],[(0,[z1,z2,z83,z287,z3,z4]),(0,[z1,z2,z1326,z4,z8,z6]),(0,[z1,z398,z3,z4,z8,z16]),(0,[z138,z2,z3,z63,z22,z8]),(0,[z1,z149,z2,z467,z3,z4]),(0,[z1,z118,z3,z4,z201,z180]),(0,[z1,z2,z11,z212,z4,z19])],[(0,[z1,z2,z116,z3,z81,z6]),(0,[z1,z2,z3,z4,z8,z192]),(0,[z1,z2,z3,z4,z1327,z8]),(0,[z1,z144,z3,z21,z8,z284])],[(0,[z1,z2,z4,z8,z714,z6]),(0,[z1,z2,z11,z3,z4,z286]),(0,[z1,z2,z3,z4,z8,z1328]),(0,[z1,z2,z3,z4,z92,z93])],[(0,[z217,z2,z11,z85,z4,z8]),(0,[z1,z398,z184,z4,z8,z6]),(0,[z1,z2,z3,z4,z554,z8]),(0,[z1,z2,z820,z3,z4,z8]),(0,[z199,z1,z3,z4,z8,z47]),(0,[z1,z2,z3,z4,z8,z1329]),(0,[z1,z2,z11,z3,z1314,z8]),(0,[z1,z2,z378,z212,z4,z8])],[(0,[z366,z83,z3,z4,z8,z6]),(0,[z78,z1,z2,z43,z3,z6]),(0,[z1,z2,z48,z4,z108,z16]),(0,[z1,z2,z3,z4,z1280,z16])],[(0,[z130,z83,z3,z4,z8,z257]),(0,[z1,z613,z3,z275,z8,z6])]],
   [[(0,[z1,z2,z1330,z287,z3,z4])],[(0,[z1,z2,z1331,z3,z4,z8]),(0,[z1,z2,z11,z3,z4,z537]),(0,[z1,z149,z3,z4,z94,z8]),(0,[z323,z2,z3,z4,z8,z105]),(0,[z1,z2,z106,z4,z8,z47])],[(0,[z2,z85,z776,z4,z8,z6]),(0,[z1,z2,z3,z4,z1332,z6]),(0,[z1,z2,z247,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z1333])],[(0,[z223,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1334]),(0,[z1,z149,z3,z4,z60,z471]),(0,[z1,z2,z106,z4,z201,z8]),(0,[z1,z2,z3,z4,z1335,z6]),(0,[z288,z2,z11,z3,z4,z8])],[(0,[z1,z2,z1336,z3,z4,z8]),(0,[z1,z2,z3,z4,z764,z6])],[(0,[z1,z2,z1337,z4,z8,z6]),(0,[z1,z2,z11,z3,z4,z443]),(0,[z1,z1255,z3,z4,z8,z6]),(0,[z1,z2,z3,z110,z22,z8]),(0,[z1,z149,z3,z4,z459,z60]),(0,[z1,z2,z11,z3,z4,z462]),(0,[z323,z1,z2,z106,z4,z8]),(0,[z1,z2,z11,z3,z4,z19])],[(0,[z1,z2,z3,z8,z6,z1338]),(0,[z1,z2,z1339,z3,z4,z8]),(0,[z1,z2,z728,z3,z4,z6])],[(0,[z1340,z2,z3,z4,z8,z6]),(0,[z18,z1,z705,z4,z8,z6]),(0,[z1,z3,z4,z943,z60,z6])],[(0,[z1,z2,z3,z4,z8,z1341]),(0,[z1,z2,z3,z252,z8,z93])],[(0,[z1,z2,z3,z1342,z8,z6]),(0,[z1,z2,z1343,z3,z4,z8]),(0,[z1,z397,z3,z4,z8,z47])],[(0,[z1,z1344,z3,z4,z8,z6]),(0,[z1,z2,z794,z4,z8,z16]),(0,[z1,z2,z41,z4,z8,z12])],[(0,[z392,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z1345]),(0,[z1,z2,z1346,z4,z8,z6]),(0,[z1,z3,z4,z8,z153,z193]),(0,[z1,z3,z4,z8,z6,z1347])],[(0,[z282,z2,z85,z4,z8,z6]),(0,[z1,z610,z3,z4,z8,z16]),(0,[z1,z149,z2,z29,z3,z4]),(0,[z1,z2,z4,z8,z739,z6]),(0,[z1,z2,z3,z119,z81,z6])],[(0,[z1,z2,z841,z3,z4,z8]),(0,[z1348,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z16,z1254])],[(0,[z1,z2,z58,z3,z4,z8]),(0,[z1,z1349,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1350]),(0,[z1,z219,z3,z4,z180,z6]),(0,[z1,z289,z3,z4,z8,z47])],[(0,[z1,z149,z4,z316,z60,z6]),(0,[z1,z2,z3,z4,z8,z715]),(0,[z1,z2,z1301,z3,z8,z16]),(0,[z1,z287,z3,z4,z47,z16]),(0,[z1,z2,z41,z4,z8,z255]),(0,[z1,z514,z3,z4,z8,z47])]],
   [[(0,[z1,z148,z3,z4,z8,z206]),(1,[z2,z3,z4,z793,z6]),(0,[z365,z2,z277,z3,z4,z8])],[(0,[z1,z2,z745,z4,z8,z6]),(0,[z1,z2,z4,z8,z6,z814]),(0,[z1,z230,z3,z4,z8,z16])],[(0,[z1,z2,z184,z4,z8,z47]),(0,[z1,z2,z1351,z4,z8,z6]),(0,[z392,z2,z3,z4,z8,z320]),(0,[z392,z2,z3,z4,z8,z321]),(0,[z1,z2,z3,z4,z8,z1352]),(0,[z1,z2,z3,z134,z8,z172])],[(0,[z1,z2,z1353,z3,z4,z8])],[(0,[z1,z2,z1354,z3,z4,z8]),(0,[z1,z2,z3,z8,z750,z6]),(0,[z288,z2,z3,z81,z8,z6])],[(0,[z1,z2,z3,z4,z8,z1355]),(0,[z1,z2,z40,z4,z45,z6]),(0,[z1,z2,z754,z4,z8,z6]),(0,[z1,z2,z1356,z3,z4,z8]),(0,[z1,z2,z287,z3,z10,z4])],[(0,[z1,z2,z3,z4,z1357,z8]),(0,[z1,z2,z424,z11,z3,z4]),(0,[z1,z159,z4,z8,z255,z16])],[(0,[z2,z3,z4,z8,z793,z6]),(0,[z1,z2,z3,z678,z8,z172]),(0,[z1,z2,z1358,z3,z4,z8]),(0,[z146,z1,z2,z287,z3,z4]),(0,[z1,z2,z1087,z11,z4,z8])],[(0,[z1,z2,z85,z4,z111,z6]),(0,[z1,z2,z3,z4,z111,z16]),(0,[z1,z2,z3,z4,z8,z1359]),(0,[z1,z2,z106,z4,z8,z172])],[(0,[z130,z83,z3,z4,z8,z319]),(0,[z78,z2,z51,z15,z8,z6]),(0,[z1360,z2,z3,z4,z8,z6]),(0,[z1,z26,z2,z753,z3,z4]),(0,[z1,z2,z3,z4,z92,z47])],[(0,[z1,z2,z3,z4,z8,z1361]),(0,[z1,z2,z3,z4,z8,z206]),(0,[z18,z1,z11,z27,z4,z8]),(0,[z18,z1,z27,z4,z8,z47])],[(0,[z1,z2,z3,z4,z8,z1362]),(0,[z1,z1363,z3,z4,z8,z6]),(0,[z1,z2,z3,z442,z8,z93])],[(0,[z456,z2,z147,z4,z8,z6])],[(0,[z1,z2,z147,z4,z111,z6]),(0,[z1,z1364,z3,z4,z8,z6]),(0,[z1,z2,z116,z3,z8,z6]),(0,[z1,z2,z239,z3,z4,z8])],[(0,[z1,z2,z287,z3,z4,z172]),(0,[z1,z2,z467,z3,z4,z19])],[(0,[z217,z2,z85,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1365]),(0,[z1,z2,z3,z4,z111,z320]),(0,[z1,z2,z3,z4,z111,z321]),(0,[z1,z2,z3,z1366,z8,z6]),(0,[z1,z2,z11,z3,z4,z203]),(0,[z1,z2,z88,z3,z8,z93])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 503) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 503).take 497) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1000).take 407) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1407)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [503, 497, 407] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 125).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 125).take 119).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 244).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 361).take 114).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 475).take 37).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [125, 119, 117, 114, 37] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

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

end PEqualNP.Outside.L_meta_38653

theorem PEqualNP.Outside.L_meta_38653 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808384 * 2 ^ 32 + 4006144704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808384 * 2 ^ 32 + 4006144704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38653.solve