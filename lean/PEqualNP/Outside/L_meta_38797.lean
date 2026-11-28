import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38797

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4272613544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x090000040804214a#64 ++ 0x04800002040210a5#64 ++ 0xfe80473c780fe3ff#64 ++ 0xff40239e3c07f1ff#64 : BitVec 256),
   (0x26019a51a4328ca5#64 ++ 0x1300cd28d2194652#64 ++ 0x7da3bad3a4729ce7#64 ++ 0xbed1dd69d2394e73#64 : BitVec 256),
   (0x540c2ca2c5831630#64 ++ 0x2a06165162c18b18#64 ++ 0xfbdc3ce3c7831f39#64 ++ 0x7dee1e71e3c18f9c#64 : BitVec 256),
   (0x9836c0fc02dc1bc0#64 ++ 0x4c1b607e016e0de0#64 ++ 0xd7ffc0fc07fc1fc1#64 ++ 0xebffe07e03fe0fe0#64 : BitVec 256),
   (0xe01b7f00076bc000#64 ++ 0x700dbf8003b5e000#64 ++ 0xcfffff0007ffe000#64 ++ 0xe7ffff8003fff000#64 : BitVec 256),
   (0x001ff7fb70000001#64 ++ 0x800ffbfdb8000000#64 ++ 0x3f9ffffff8000000#64 ++ 0x1fcffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 6]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [8, 12]⟩, ⟨.and, [11, 4]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x000480fb70000001 0x8002407db8000000 0x300000fff8000000 0x1800007ffc000000

def z1 : W := mkw 0x0009370370000001 0x80049b81b8000000 0x28003f03f8000000 0x14001f81fc000000

def z2 : W := mkw 0x090000040804214a 0x04800002040210a5 0xfe80473c780fe3ff 0xff40239e3c07f1ff

def z3 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x7da3bad3a4729ce7 0xbed1dd69d2394e73

def z4 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xfbdc3ce3c7831f39 0x7dee1e71e3c18f9c

def z5 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xd7ffc0fc07fc1fc1 0xebffe07e03fe0fe0

def z6 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xcfffff0007ffe000 0xe7ffff8003fff000

def z7 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x3f9ffffff8000000 0x1fcffffffc000000

def z8 : W := mkw 0x9836c0ff72dc1bc1 0xcc1b607fb96e0de0 0xf7ffc0fffffc1fc1 0xfbffe07ffffe0fe0

def z9 : W := mkw 0x0013d35930000001 0x8009e9ac98000000 0x0403c31c38000000 0x0201e18e1c000000

def z10 : W := mkw 0x541ffffbf5831631 0xaa0ffffdfac18b18 0xffdfffffff831f39 0x7fefffffffc18f9c

def z11 : W := mkw 0x1000000000801200 0x0800000000400900 0xc040000007801f01 0x6020000003c00f80

def z12 : W := mkw 0x8012400002480000 0x4009200001240000 0xc7ffc00007fc0000 0xe3ffe00003fe0000

def z13 : W := mkw 0x983ff7ff72dc1bc1 0xcc1ffbffb96e0de0 0xfffffffffffc1fc1 0xfffffffffffe0fe0

def z14 : W := mkw 0x090000040804214a 0x04800002040210a5 0x8200452c580d6318 0x410022962c06b18c

def z15 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x55ff80d007f01cc1 0xaaffc06803f80e60

def z16 : W := mkw 0x0009370370000001 0x80049b81b8000000 0x3e807f3ff8000000 0x1f403f9ffc000000

def z17 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x017f80c007f01c00 0x00bfc06003f80e00

def z18 : W := mkw 0x20011a0004228000 0x10008d0002114000 0x4da3ba0004728000 0xa6d1dd0002394000

def z19 : W := mkw 0xe61bff51a77bcca5 0x730dffa8d3bde652 0xffffffd3a7fffce7 0xffffffe9d3fffe73

def z20 : W := mkw 0xa01353000268c000 0x5009a98001346000 0x0423c300007ce000 0x8211e180003e7000

def z21 : W := mkw 0xf41f7fa2c7ebd630 0x7a0fbfd163f5eb18 0xffffffe3c7ffff39 0xfffffff1e3ffff9c

def z22 : W := mkw 0x22019a5124328885 0x1100cd2892194442 0x4da3ba10247280c6 0xa6d1dd0812394063

def z23 : W := mkw 0x001e65aa50000000 0x800f32d528000000 0x021c452c58000000 0x010e22962c000000

def z24 : W := mkw 0xe01f7fa2476bc000 0x700fbfd123b5e000 0xffffffe3c7ffe000 0xfffffff1e3fff000

def z25 : W := mkw 0x182480ff70941bc1 0x8c12407fb84a0de0 0x300000fff8001fc1 0x1800007ffc000fe0

def z26 : W := mkw 0x0400080084020420 0x0200040042010210 0x798038c384021c21 0x3cc01c61c2010e10

def z27 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xffffc7fc7fffffff 0xffffe3fe3fffffff

def z28 : W := mkw 0x500c24a241811210 0x2806125120c08908 0x825c042043810318 0x412e021021c0818c

def z29 : W := mkw 0x601ffffb7523c001 0xb00ffffdba91e000 0x3f9ffffff803e000 0x1fcffffffc01f000

def z30 : W := mkw 0x090000040804214a 0x04800002040210a5 0xf680403c780c03ff 0xfb40201e3c0601ff

def z31 : W := mkw 0x9820000402dc1bc0 0x4c100002016e0de0 0xd6e0403c07fc1fc1 0xeb70201e03fe0fe0

def z32 : W := mkw 0x0001925120000001 0x0000c92890000000 0x3d83bad3a0000000 0x1ec1dd69d0000000

def z33 : W := mkw 0x0000805930000001 0x8000402c98000000 0x0000001c38000000 0x0000000e1c000000

def z34 : W := mkw 0xe0124800076bc000 0x7009240003b5e000 0xc7ffc00007ffe000 0xe3ffe00003fff000

def z35 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x311fb8fff8000000 0x188fdc7ffc000000

def z36 : W := mkw 0x100400a000801200 0x0802005000400900 0xd3dc00e007801f01 0x69ee007003c00f80

def z37 : W := mkw 0x26011a01a4228425 0x13008d00d2114212 0x28003a03a0028026 0x14001d01d0014013

def z38 : W := mkw 0xe0000800076bc000 0x7000040003b5e000 0xc060000007ffe000 0xe030000003fff000

def z39 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0x017fb80007f00000 0x00bfdc0003f80000

def z40 : W := mkw 0x0000000000000000 0x0000000000000000 0x7c800210200280e7 0xbe40010810014073

def z41 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x7f9ffffff80280e7 0xbfcffffffc014073

def z42 : W := mkw 0x010000000800200a 0x0080000004001005 0x000000000003e03e 0x000000000001f01f

def z43 : W := mkw 0x590c24a64985335a 0x2c86125324c299ad 0xfedc473c7b8fe3ff 0xff6e239e3dc7f1ff

def z44 : W := mkw 0x001bf75b70000001 0x800dfbadb8000000 0x2c03ff1ff8000000 0x1601ff8ffc000000

def z45 : W := mkw 0x0913d35d3804214b 0x8489e9ae9c0210a5 0x0403c31c380ce0c6 0x8201e18e1c067063

def z46 : W := mkw 0x261ffffbf4328ca5 0x930ffffdfa194652 0x7fbffffffc729ce7 0xbfdffffffe394e73

def z47 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0x015c38c387801c00 0x00ae1c61c3c00e00

def z48 : W := mkw 0x760dbef3e5b39eb5 0x3b06df79f2d9cf5a 0xffffbef3e7f39fff 0xffffdf79f3f9cfff

def z49 : W := mkw 0x090000040804214a 0x04800002040210a5 0x2c00471c780fe0fe 0x9600238e3c07f07f

def z50 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0x38003ce3c0031f39 0x1c001e71e0018f9c

def z51 : W := mkw 0x000c24a240000000 0x0006125120000000 0xfb9c3ce3c0030339 0x7dce1e71e001819c

def z52 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x011fb8c380000000 0x008fdc61c0000000

def z53 : W := mkw 0x541eecfac5831630 0x2a0f767d62c18b18 0xffdffcffc7831f39 0x7feffe7fe3c18f9c

def z54 : W := mkw 0x0000000000000000 0x0000000000000000 0xfa80042040030339 0x7d4002102001819c

def z55 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0x057fc0dc07fc1cc0 0x82bfe06e03fe0e60

def z56 : W := mkw 0xf83b7f0407ffdbc0 0x7c1dbf8203ffede0 0xcfffff0007ffffc1 0xe7ffff8003ffffe0

def z57 : W := mkw 0x760dbef3e5b39eb5 0x3b06df79f2d9cf5a 0x7dffbad3a7f29ce7 0xbeffdd69d3f94e73

def z58 : W := mkw 0x993640ac0acc334a 0x4c9b2056056619a5 0x825c452c5b8d6318 0x412e22962dc6b18c

def z59 : W := mkw 0x903ff7fb72d81a81 0xc81ffbfdb96c0d40 0x3ffffffffff01c00 0x1ffffffffff80e00

def z60 : W := mkw 0x60093e0005238000 0x30049f000291c000 0xcfffbe0007f38000 0xe7ffdf0003f9c000

def z61 : W := mkw 0x2f019a55ac36adef 0x1780cd2ad61b56f7 0xffa3fffffc7fffff 0xffd1fffffe3fffff

def z62 : W := mkw 0x36059af1a4b29ea5 0x1b02cd78d2594f52 0xffffbaf3a7f29fe7 0xffffdd79d3f94ff3

def z63 : W := mkw 0x091ff7ff7804214b 0x848ffbffbc0210a5 0xff9ffffff80fe3ff 0xffcffffffc07f1ff

def z64 : W := mkw 0x5d1ffffffd87377b 0xae8ffffffec39bbd 0xffdfffffff8fffff 0xffefffffffc7ffff

def z65 : W := mkw 0x090000040804214a 0x04800002040210a5 0xc0000000000fe3ff 0xe00000000007f1ff

def z66 : W := mkw 0x100480f000901a80 0x0802407800480d40 0xd7ff80f007f01fc1 0xebffc07803f80fe0

def z67 : W := mkw 0x8932c05c0a5c29ca 0x4499602e052e14e5 0xfea3c73c787fe3ff 0xff51e39e3c3ff1ff

def z68 : W := mkw 0x2f019a55ac36adef 0x1780cd2ad61b56f7 0xfda3bad3a47fffff 0xfed1dd69d23fffff

def z69 : W := mkw 0x5400080085831630 0x2a00040042c18b18 0xc040000007831f39 0x6020000003c18f9c

def z70 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0xff9ffffff8030339 0x7fcffffffc01819c

def z71 : W := mkw 0xc01a650003494000 0x600d328001a4a000 0x825c4500038d6000 0x412e228001c6b000

def z72 : W := mkw 0x0001130130000001 0x8000898098000000 0x0000030038000000 0x000001801c000000

def z73 : W := mkw 0x9820000402dc1bc0 0x4c100002016e0de0 0xc060000007fc1fc1 0xe030000003fe0fe0

def z74 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0xd3ff80e007f01f01 0x69ffc07003f80f80

def z75 : W := mkw 0x0016c0f800000000 0x000b607c00000000 0x3f9fc7fc78000000 0x1fcfe3fe3c000000

def z76 : W := mkw 0xd41e6ca2c7cb1630 0x6a0f365163e58b18 0xfffffce3c7ff1f39 0xfffffe71e3ff8f9c

def z77 : W := mkw 0x182480fc00941bc0 0x0c12407e004a0de0 0x100000fc00001fc1 0x0800007e00000fe0

def z78 : W := mkw 0x60093f000523c000 0x30049f800291e000 0x08003f000003e000 0x04001f800001f000

def z79 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xffffc4fc47ff1ff9 0xffffe27e23ff8ffc

def z80 : W := mkw 0xe91b7f040f6fe14a 0x748dbf8207b7f0a5 0xffffff3c7fffe3ff 0xffffff9e3ffff1ff

def z81 : W := mkw 0x540cacf2c5931eb0 0x2a06567962c98f58 0xffffbcf3c7f31ff9 0xffffde79e3f98ffc

def z82 : W := mkw 0x141ff7fbf0801631 0x8a0ffbfdf8400b18 0x3f9ffffff8001f39 0x1fcffffffc000f9c

def z83 : W := mkw 0xe01ffffb776bc001 0xf00ffffdbbb5e000 0xffffffffffffe000 0xfffffffffffff000

def z84 : W := mkw 0x2f0008048c36adee 0x17800402461b56f7 0xc0200000047fffff 0xe0100000023fffff

def z85 : W := mkw 0xe61bff51a77bcca5 0x730dffa8d3bde652 0x7dffbad3a7f29ce7 0xbeffdd69d3f94e73

def z86 : W := mkw 0xe01b77000369c000 0x700dbb8001b4e000 0x867fc70003fde000 0xc33fe38001fef000

def z87 : W := mkw 0xa01ff7fb7268c001 0xd00ffbfdb9346000 0x3fbffffff87ce000 0x9fdffffffc3e7000

def z88 : W := mkw 0x8833d35d325c09c1 0xc419e9ae992e04e0 0x0423c31c387c00c0 0x8211e18e1c3e0060

def z89 : W := mkw 0x7600080085b39eb4 0x3b00040042d9cf5a 0xc060000007f39fff 0xe030000003f9cfff

def z90 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x7fa3fffffc729ce7 0xbfd1fffffe394e73

def z91 : W := mkw 0x54082c02c5831630 0x2a04160162c18b18 0xe8403c03c7831f39 0x74201e01e3c18f9c

def z92 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xffdc3ef3e7839fff 0xffee1f79f3c1cfff

def z93 : W := mkw 0x0000000000000000 0x0000000000000000 0x080007000003e000 0x040003800001f000

def z94 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0xff9ffffff80fe000 0xffcffffffc07f000

def z95 : W := mkw 0x001ff7fb70100881 0x800ffbfdb8080440 0x7fbffffffc701cc1 0xbfdffffffe380e60

def z96 : W := mkw 0x090000040804214a 0x04800002040210a5 0xce80472c580fe318 0xe74023962c07f18c

def z97 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x0123b8c384701c00 0x0091dc61c2380e00

def z98 : W := mkw 0x000c24a240000000 0x0006125120000000 0x3b9c3ce3c0000000 0x1dce1e71e0000000

def z99 : W := mkw 0x9832400402dc1bc0 0x4c192002016e0de0 0xc7ffc00007fc1fc1 0xe3ffe00003fe0fe0

def z100 : W := mkw 0x60093f000523c000 0x30049f800291e000 0xcbdc3f000783e000 0x65ee1f8003c1f000

def z101 : W := mkw 0x45082c02cd03243a 0x228416016681921d 0x28003f03f803e03e 0x14001f81fc01f01f

def z102 : W := mkw 0x100400a000801200 0x0802005000400900 0x015c00c007801c00 0x00ae006003c00e00

def z103 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xf7ffc0fc7ffc1fff 0xfbffe07e3ffe0fff

def z104 : W := mkw 0xc01a6c00074b0000 0x600d360003a58000 0xcffffc0007ff0000 0xe7fffe0003ff8000

def z105 : W := mkw 0x44082c02c5030430 0x2204160162818218 0x28003c03c0030038 0x14001e01e001801c

def z106 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe80473c780fe000 0xff40239e3c07f000

def z107 : W := mkw 0x140c24a2c0801630 0x0a06125160400b18 0x3b9c3ce3c0001f39 0x1dce1e71e0000f9c

def z108 : W := mkw 0x000c24a240000000 0x0006125120000000 0x3f9c7ffff8000000 0x1fce3ffffc000000

def z109 : W := mkw 0x5d0c2ca6cd87377a 0x2e86165366c39bbd 0xffdc7fffff8fffff 0xffee3fffffc7ffff

def z110 : W := mkw 0x100400a000801200 0x0802005000400900 0xfbdc04e047831f39 0x7dee027023c18f9c

def z111 : W := mkw 0x0000805000100880 0x0000402800080440 0x55a380d004701cc1 0xaad1c06802380e60

def z112 : W := mkw 0xd83ee5fc03dd5bc0 0x6c1f72fe01eeade0 0xd7ffc5fc07fd7fc1 0xebffe2fe03febfe0

def z113 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x031ffdefd8000000 0x018ffef7ec000000

def z114 : W := mkw 0x541ffffbf5831631 0xaa0ffffdfac18b18 0x3fdfffffff801c00 0x1fefffffffc00e00

def z115 : W := mkw 0x0800000400040140 0x04000002000200a0 0xd680403c000c03c1 0xeb40201e000601e0

def z116 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xdfffc7fc07ffffc1 0xefffe3fe03ffffe0

def z117 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0x117f80fc07f01fc1 0x08bfc07e03f80fe0

def z118 : W := mkw 0x501ff7fb71811211 0xa80ffbfdb8c08908 0xbfdffffffb810318 0x5feffffffdc0818c

def z119 : W := mkw 0x000ca4fb70000001 0x8006527db8000000 0x3b9c3cfff8000000 0x1dce1e7ffc000000

def z120 : W := mkw 0x2600080084328ca4 0x1300040042194652 0x4020000004729ce7 0xa010000002394e73

def z121 : W := mkw 0x2617daf9a4328ca5 0x130bed7cd2194652 0x7fbffaffa4729ce7 0xbfdffd7fd2394e73

def z122 : W := mkw 0x0000805000100880 0x0000402800080440 0x7da382d024729ce7 0xbed1c16812394e73

def z123 : W := mkw 0x091ff7ff7804214b 0x848ffbffbc0210a5 0xbf9ffffff80d6318 0x5fcffffffc06b18c

def z124 : W := mkw 0x0000000000000000 0x0000000000000000 0x8200042040010318 0x410002102000818c

def z125 : W := mkw 0x0000000000000000 0x0000000000000000 0xce804700000fe000 0xe74023800007f000

def z126 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0xffa3ffd3a47ffce7 0xffd1ffe9d23ffe73

def z127 : W := mkw 0x2201925120308885 0x1100c92890184442 0x04238210207080c6 0x8211c10810384063

def z128 : W := mkw 0x0000805000000000 0x0000402800000000 0x158380d000000000 0x0ac1c06800000000

def z129 : W := mkw 0x0800000400040140 0x04000002000200a0 0xfe80473c780c03c1 0xff40239e3c0601e0

def z130 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0x057ffb0007fce000 0x82bffd8003fe7000

def z131 : W := mkw 0x26011a01a4228425 0x13008d00d2114212 0x7c803a13a00280e7 0xbe401d09d0014073

def z132 : W := mkw 0x8012c05002580880 0x40096028012c0440 0xd7ffc0d007fc1cc1 0xebffe06803fe0e60

def z133 : W := mkw 0x0800000400040140 0x04000002000200a0 0xc0000000000c03c1 0xe0000000000601e0

def z134 : W := mkw 0x0001120000000000 0x0000890000000000 0x0d83ba0000000000 0x06c1dd0000000000

def z135 : W := mkw 0x000480f800000000 0x0002407c00000000 0x100000fc00000000 0x0800007e00000000

def z136 : W := mkw 0x903640a802c81200 0x481b205401640900 0x005c000003800000 0x002e000001c00000

def z137 : W := mkw 0x760c2ca2c5b39eb4 0x3b06165162d9cf5a 0xfbfc3ce3c7f39fff 0xfdfe1e71e3f9cfff

def z138 : W := mkw 0x0000000000000000 0x0000000000000000 0x54800010000000c1 0xaa40000800000060

def z139 : W := mkw 0x500c24a241811210 0x2806125120c08908 0xfadc042043830339 0x7d6e021021c1819c

def z140 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x0523bad3a4709cc6 0x8291dd69d2384e63

def z141 : W := mkw 0xc01a650003494000 0x600d328001a4a000 0xc7ffc50007fd6000 0xe3ffe28003feb000

def z142 : W := mkw 0x0017d3f930000001 0x800be9fc98000000 0x179fc3fc38000000 0x0bcfe1fe1c000000

def z143 : W := mkw 0x883ff7ff725c09c1 0xc41ffbffb92e04e0 0x3fbffffff87c00c0 0x9fdffffffc3e0060

def z144 : W := mkw 0x801b770002480000 0x400dbb8001240000 0xcfffff0007fc0000 0xe7ffff8003fe0000

def z145 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0x837fc0ec07fc1f00 0x41bfe07603fe0f80

def z146 : W := mkw 0x44082c02c5030430 0x2204160162818218 0x0000380380000000 0x00001c01c0000000

def z147 : W := mkw 0x983640ac02cc1340 0x4c1b2056016609a0 0x825c402c038c0300 0x412e201601c60180

def z148 : W := mkw 0x40082c0005030000 0x2004160002818000 0xcbdc3c0007830000 0x65ee1e0003c18000

def z149 : W := mkw 0xf83ffffc07ffdbc0 0x7c1ffffe03ffede0 0xdffffffc07ffffc1 0xeffffffe03ffffe0

def z150 : W := mkw 0x0000000000000000 0x0000000000000000 0x3e80473c78000000 0x1f40239e3c000000

def z151 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x4123b8c384729ce7 0xa091dc61c2394e73

def z152 : W := mkw 0x0016c0f800000000 0x000b607c00000000 0x179fc0fc00000000 0x0bcfe07e00000000

def z153 : W := mkw 0xf836c8fc07ffdbc0 0x7c1b647e03ffede0 0xd7ffc0fc07ffffc1 0xebffe07e03ffffe0

def z154 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xd3dc38e387801f01 0x69ee1c71c3c00f80

def z155 : W := mkw 0x183ff7ff70941bc1 0x8c1ffbffb84a0de0 0x3f9ffffff8001fc1 0x1fcffffffc000fe0

def z156 : W := mkw 0x600008000523c000 0x300004000291e000 0x000000000003e000 0x000000000001f000

def z157 : W := mkw 0x010000000800200a 0x0080000004001005 0x280007007803e03e 0x140003803c01f01f

def z158 : W := mkw 0x983ff7ff72cc1341 0xcc1ffbffb96609a0 0xbfdffffffb8c0300 0x5feffffffdc60180

def z159 : W := mkw 0x190400a40884334a 0x0c820052044219a5 0xffdc47fc7f8fffff 0xffee23fe3fc7ffff

def z160 : W := mkw 0x0000000000000000 0x0000000000000000 0xd280002000000301 0x6940001000000180

def z161 : W := mkw 0x090000040804214a 0x04800002040210a5 0x0400431c380ce0c6 0x8200218e1c067063

def z162 : W := mkw 0x2201925120308885 0x1100c92890184442 0x7ca38210207280e7 0xbe51c10810394073

def z163 : W := mkw 0x000480fb70000001 0x8002407db8000000 0x3e8047fff8000000 0x1f4023fffc000000

def z164 : W := mkw 0x000db7fb70000001 0x8006dbfdb8000000 0x38003ffff8000000 0x1c001ffffc000000

def z165 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x38003ad3a0029ce7 0x1c001d69d0014e73

def z166 : W := mkw 0x2f1ffffffc36adef 0x978ffffffe1b56f7 0xffbffffffc7fffff 0xffdffffffe3fffff

def z167 : W := mkw 0x8832c05c025c09c0 0x4419602e012e04e0 0x0423c01c007c00c0 0x8211e00e003e0060

def z168 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xffffff3c7fffe000 0xffffff9e3ffff000

def z169 : W := mkw 0x401b7f0005030000 0x200dbf8002818000 0xcfdfff0007830000 0x67efff8003c18000

def z170 : W := mkw 0x20011a0004228000 0x10008d0002114000 0xcfa3ff00047fe000 0xe7d1ff80023ff000

def z171 : W := mkw 0x26011a01a4228425 0x13008d00d2114212 0x6da3ba03a4728026 0xb6d1dd01d2394013

def z172 : W := mkw 0x1016c0f800801200 0x080b607c00400900 0xd7dfc0fc07801f01 0x6befe07e03c00f80

def z173 : W := mkw 0x2609bf53f4328ca5 0x9304dfa9fa194652 0x7da3bfd3fc729ce7 0xbed1dfe9fe394e73

def z174 : W := mkw 0x0000000000000000 0x0000000000000000 0xca80040000030000 0x6540020000018000

def z175 : W := mkw 0x010000000800200a 0x0080000004001005 0xfa8007207803e33f 0x7d4003903c01f19f

def z176 : W := mkw 0x9020000002d81a80 0x48100000016c0d40 0x0060000007f01c00 0x0030000003f80e00

def z177 : W := mkw 0xdc36c8fc87df1ff0 0x6e1b647e43ef8ff8 0xd7ffc0fc07ff1ff9 0xebffe07e03ff8ffc

def z178 : W := mkw 0x090000040804214a 0x04800002040210a5 0x3e80473c780003ff 0x1f40239e3c0001ff

def z179 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0xffa3bef3e4739fff 0xffd1df79f239cfff

def z180 : W := mkw 0xe61b7f01a76bc425 0x730dbf80d3b5e212 0xefffff03a7ffe026 0xf7ffff81d3fff013

def z181 : W := mkw 0x500c2ca245831210 0x2806165122c18908 0xcbdc3c2047830318 0x65ee1e1023c1818c

def z182 : W := mkw 0x6609be51a5338ca5 0x3304df28d299c652 0xffffbed3a7f39ce7 0xffffdf69d3f9ce73

def z183 : W := mkw 0x0000000000000000 0x0000000000000000 0x1680403c00000000 0x0b40201e00000000

def z184 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xffffc7fc7ffc1fc1 0xffffe3fe3ffe0fe0

def z185 : W := mkw 0x992000040adc3bca 0x4c900002056e1de5 0xfee0473c7fffffff 0xff70239e3fffffff

def z186 : W := mkw 0x0000000000000000 0x0000000000000000 0x45a3800004700000 0xa2d1c00002380000

def z187 : W := mkw 0x140408a2c4821630 0x0a02045162410b18 0x798038e3c4021f39 0x3cc01c71e2010f9c

def z188 : W := mkw 0x993ff7ff7adc3bcb 0xcc9ffbffbd6e1de5 0xffffffffffffffff 0xffffffffffffffff

def z189 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0x835c3ce3c7811f18 0x41ae1e71e3c08f8c

def z190 : W := mkw 0x5d0008048d87377a 0x2e80040246c39bbd 0xc0400000078fffff 0xe020000003c7ffff

def z191 : W := mkw 0xe0093f00076bc000 0x70049f8003b5e000 0xc8603f0007ffe000 0xe4301f8003fff000

def z192 : W := mkw 0x8012400002480000 0x4009200001240000 0x0423c000007c0000 0x8211e000003e0000

def z193 : W := mkw 0xf820080407ffdbc0 0x7c10040203ffede0 0xc060000007ffffc1 0xe030000003ffffe0

def z194 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xd7ffc5fc5ffd7fd9 0xebffe2fe2ffebfec

def z195 : W := mkw 0x9e36c0fda2dc1fe5 0x4f1b607ed16e0ff2 0xf7ffc0ffa7fc1fe7 0xfbffe07fd3fe0ff3

def z196 : W := mkw 0xd43eecfac7db1eb0 0x6a1f767d63ed8f58 0x017fb8c387f01c00 0x00bfdc61c3f80e00

def z197 : W := mkw 0x261ffffbf4328ca5 0x930ffffdfa194652 0x7dbfbad3a4729ce7 0xbedfdd69d2394e73

def z198 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x2923bac3a4729c26 0x1491dd61d2394e13

def z199 : W := mkw 0x090000040804214a 0x04800002040210a5 0x3000003c780003ff 0x1800001e3c0001ff

def z200 : W := mkw 0x44093f03f5030431 0xa2049f81fa818218 0x28003f03f8030038 0x14001f81fc01801c

def z201 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x4da3bac384729c00 0xa6d1dd61c2394e00

def z202 : W := mkw 0x090000040804214a 0x04800002040210a5 0xfa80452c580f6339 0x7d4022962c07b19c

def z203 : W := mkw 0x061ff7fbf0100ca5 0x830ffbfdf8080652 0x3f9ffffff8001ce7 0x1fcffffffc000e73

def z204 : W := mkw 0xe83bff5c077fc9c0 0x741dffae03bfe4e0 0xcfffff1c07ffe0c0 0xe7ffff8e03fff060

def z205 : W := mkw 0x0000000000000000 0x0000000000000000 0x3a80042040000000 0x1d40021020000000

def z206 : W := mkw 0x8932c05c0a5c29ca 0x4499602e052e14e5 0x0423c31c387ce0c6 0x8211e18e1c3e7063

def z207 : W := mkw 0x0017d3fb70000001 0x800be9fdb8000000 0x3403c3fff8000000 0x1a01e1fffc000000

def z208 : W := mkw 0x801ff7fb72480001 0xc00ffbfdb9240000 0xfffffffffffc0000 0xfffffffffffe0000

def z209 : W := mkw 0xbe3ffffff6fe9fe5 0xdf1ffffffb7f4ff2 0xfffffffffffe9fe7 0xffffffffffff4ff3

def z210 : W := mkw 0x0001925120000001 0x0000c92890000000 0x7d83bad3a00280e7 0xbec1dd69d0014073

def z211 : W := mkw 0x8012400002480000 0x4009200001240000 0xcfffc70007ffe000 0xe7ffe38003fff000

def z212 : W := mkw 0x540d3fa3f5831631 0xaa069fd1fac18b18 0xfbdc3fe3ff831f39 0x7dee1ff1ffc18f9c

def z213 : W := mkw 0xdd3eecfecfdf3ffa 0x6e9f767f67ef9ffd 0xffffffffffffffff 0xffffffffffffffff

def z214 : W := mkw 0x8832400c024c0140 0x44192006012600a0 0x0000400c000c0000 0x0000200600060000

def z215 : W := mkw 0x5d0c2ca6cd87377a 0x2e86165366c39bbd 0xfbdc3ce3c78fffff 0xfdee1e71e3c7ffff

def z216 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xc17fb80007ffe000 0xe0bfdc0003fff000

def z217 : W := mkw 0x9837d3fd32dc1bc1 0xcc1be9fe996e0de0 0xd7ffc3fc3ffc1fc1 0xebffe1fe1ffe0fe0

def z218 : W := mkw 0xa013d3593268c001 0xd009e9ac99346000 0x0423c31c387ce000 0x8211e18e1c3e7000

def z219 : W := mkw 0x06000001a0000425 0x03000000d0000212 0x20000003a0000026 0x10000001d0000013

def z220 : W := mkw 0x66093f01a523c425 0x33049f80d291e212 0x28003f03a003e026 0x14001f81d001f013

def z221 : W := mkw 0xe01b7f03776bc001 0xf00dbf81bbb5e000 0xefffff03ffffe000 0xf7ffff81fffff000

def z222 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x061fc73c78000000 0x030fe39e3c000000

def z223 : W := mkw 0x001b770000000000 0x000dbb8000000000 0x0f9fff0000000000 0x07cfff8000000000

def z224 : W := mkw 0xf01f7fa247ebd210 0x780fbfd123f5e908 0xcfffff2047ffe318 0xe7ffff9023fff18c

def z225 : W := mkw 0x44082c02c5030430 0x2204160162818218 0xebdc3c03c7830038 0x75ee1e01e3c1801c

def z226 : W := mkw 0x0000805000100880 0x0000402800080440 0x012380c004701c00 0x0091c06002380e00

def z227 : W := mkw 0x8832c05c025c09c0 0x4419602e012e04e0 0x55a3c0dc047c1cc1 0xaad1e06e023e0e60

def z228 : W := mkw 0xd41e6da2c7cb5630 0x6a0f36d163e5ab18 0xfbdc7de3c78f7f39 0x7dee3ef1e3c7bf9c

def z229 : W := mkw 0x88200004025c09c0 0x44100002012e04e0 0x00200000007c00c0 0x80100000003e0060

def z230 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xcbdc3cc387831c00 0x65ee1e61c3c18e00

def z231 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xc17f80c007fc1fc1 0xe0bfc06003fe0fe0

def z232 : W := mkw 0x2f0008048c36adee 0x17800402461b56f7 0xfea0473c7c7fffff 0xff50239e3e3fffff

def z233 : W := mkw 0xa01353000268c000 0x5009a98001346000 0xcea3c700007fe000 0xe751e380003ff000

def z234 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0x097fbf0007f3e000 0x04bfdf8003f9f000

def z235 : W := mkw 0xe01ffffb776bc001 0xf00ffffdbbb5e000 0x017fb8c387f00000 0x00bfdc61c3f80000

def z236 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x051ffbdfb8000000 0x028ffdefdc000000

def z237 : W := mkw 0x140400a2c0801630 0x0a02005160400b18 0x300000e3c0001f39 0x18000071e0000f9c

def z238 : W := mkw 0x60093f000523c000 0x30049f800291e000 0xce807f00000fe000 0xe7403f800007f000

def z239 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000000280e7 0xa000000000014073

def z240 : W := mkw 0x26093f03f4228425 0x93049f81fa114212 0x28003f03f8028026 0x14001f81fc014013

def z241 : W := mkw 0x090937077804214b 0x84849b83bc0210a5 0xfe807f3ff80fe3ff 0xff403f9ffc07f1ff

def z242 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0x837ffd0007fd6000 0x41bffe8003feb000

def z243 : W := mkw 0xc01ff7fb73494001 0xe00ffbfdb9a4a000 0xbfdffffffb8d6000 0x5feffffffdc6b000

def z244 : W := mkw 0xf41f7fa2c7ebd630 0x7a0fbfd163f5eb18 0xcfffffc387fffc00 0xe7ffffe1c3fffe00

def z245 : W := mkw 0x041ffffbf4020421 0x820ffffdfa010210 0x7f9ffffffc021c21 0x3fcffffffe010e10

def z246 : W := mkw 0x400c2ca245030000 0x2006165122818000 0xfbdc3ce3c7830000 0x7dee1e71e3c18000

def z247 : W := mkw 0x0800000400040140 0x04000002000200a0 0x0400401c000c00c0 0x8200200e00060060

def z248 : W := mkw 0x260dbef3e4328ca5 0x1306df79f2194652 0x7fbfbef3e4729ce7 0xbfdfdf79f2394e73

def z249 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c80020000028000 0xa640010000014000

def z250 : W := mkw 0x090000040804214a 0x04800002040210a5 0xd680453c580d63d9 0xeb40229e2c06b1ec

def z251 : W := mkw 0xf83f7fac07efd340 0x7c1fbfd603f7e9a0 0xcfffff2c07ffe300 0xe7ffff9603fff180

def z252 : W := mkw 0xdc3e6caec7cf1770 0x6e1f365763e78bb8 0xfbdc7cefc78f1f39 0x7dee3e77e3c78f9c

def z253 : W := mkw 0x090192552804214b 0x0480c92a940210a5 0xff83fffff80fe3ff 0xffc1fffffc07f1ff

def z254 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000002040000339 0x180000102000019c

def z255 : W := mkw 0x221ff7fb70308885 0x910ffbfdb8184442 0x3fbffffff87080c6 0x9fdffffffc384063

def z256 : W := mkw 0x0000000000000000 0x0000000000000000 0x398038c380000000 0x1cc01c61c0000000

def z257 : W := mkw 0x5d0008048d87377a 0x2e80040246c39bbd 0xfec0473c7f8fffff 0xff60239e3fc7ffff

def z258 : W := mkw 0x090000040804214a 0x04800002040210a5 0xd680433c380ce3c7 0xeb40219e1c0671e3

def z259 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe804720400fe339 0xff4023902007f19c

def z260 : W := mkw 0x0400080084020420 0x0200040042010210 0x2800380380020020 0x14001c01c0010010

def z261 : W := mkw 0x08008054001409c0 0x0400402a000a04e0 0xd7a3c0fc047c1fc1 0xebd1e07e023e0fe0

def z262 : W := mkw 0x102480f800901a80 0x0812407c00480d40 0x000000c000001c00 0x0000006000000e00

def z263 : W := mkw 0x760d3ea3e5a39635 0x3b069f51f2d1cb1a 0xfbdc3ee3e7839f3f 0x7dee1f71f3c1cf9f

def z264 : W := mkw 0x0000000000000000 0x0000000000000000 0x04000210200080c6 0x8200010810004063

def z265 : W := mkw 0x0000000000000000 0x0000000000000000 0x2800040040030038 0x140002002001801c

def z266 : W := mkw 0x2001120000208000 0x1000890000104000 0x0423820000708000 0x8211c10000384000

def z267 : W := mkw 0x2201925120308885 0x1100c92890184442 0x55a382d024709cc7 0xaad1c16812384e63

def z268 : W := mkw 0x090000040804214a 0x04800002040210a5 0x0000002c58000318 0x000000162c00018c

def z269 : W := mkw 0xe61bff51a77bcca5 0x730dffa8d3bde652 0xcfffffc387fffc00 0xe7ffffe1c3fffe00

def z270 : W := mkw 0xd83eecfc07df1bc0 0x6c1f767e03ef8de0 0xdffffcfc07ff1fc1 0xeffffe7e03ff8fe0

def z271 : W := mkw 0x983ff7ff72dc1bc1 0xcc1ffbffb96e0de0 0xd7fff8ff87fc1fc1 0xebfffc7fc3fe0fe0

def z272 : W := mkw 0x010000000800200a 0x0080000004001005 0x3e80473c7803e03e 0x1f40239e3c01f01f

def z273 : W := mkw 0x9c36c8fc86de1fe0 0x4e1b647e436f0ff0 0xfffff8ff87fe1fe1 0xfffffc7fc3ff0ff0

def z274 : W := mkw 0x090000040804214a 0x04800002040210a5 0xf000003c780fe3ff 0xf800001e3c07f1ff

def z275 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xffffff2047ffe339 0xffffff9023fff19c

def z276 : W := mkw 0x0008240000000000 0x0004120000000000 0x0b9c3c0000000000 0x05ce1e0000000000

def z277 : W := mkw 0x40082c0005030000 0x2004160002818000 0xcfdc7f00078fe000 0xe7ee3f8003c7f000

def z278 : W := mkw 0x261ffffbf4228425 0x930ffffdfa114212 0x3f9ffffff8028026 0x1fcffffffc014013

def z279 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0x925c40fc038c1fc1 0x492e207e01c60fe0

def z280 : W := mkw 0x101ff7fb70801201 0x880ffbfdb8400900 0xffdfffffff801f01 0x7fefffffffc00f80

def z281 : W := mkw 0x76019a51a5b39eb5 0x3b00cd28d2d9cf5a 0xfde3bad3a7f39fff 0xfef1dd69d3f9cfff

def z282 : W := mkw 0x5d0c2ca6cd87377a 0x2e86165366c39bbd 0xfbdc3cffff831fff 0x7dee1e7fffc18fff

def z283 : W := mkw 0x182480fc00941bc0 0x0c12407e004a0de0 0xd68040fc000c1fc1 0xeb40207e00060fe0

def z284 : W := mkw 0x261bff51a4328ca5 0x130dffa8d2194652 0x7fbfffd3a4729ce7 0xbfdfffe9d2394e73

def z285 : W := mkw 0xc01a650003494000 0x600d328001a4a000 0x005c000003800000 0x002e000001c00000

def z286 : W := mkw 0x140408a084821620 0x0a02045042410b10 0xfbdc38e387821f21 0x7dee1c71c3c10f90

def z287 : W := mkw 0x500c24a241811210 0x2806125120c08908 0xbbdc3ce3c3810318 0x5dee1e71e1c0818c

def z288 : W := mkw 0x0000000000000000 0x0000000000000000 0x7880000000020021 0x3c40000000010010

def z289 : W := mkw 0x2201925120308885 0x1100c92890184442 0x0023800000700000 0x0011c00000380000

def z290 : W := mkw 0x0013d35930000001 0x8009e9ac98000000 0x3d83fbdfb8000000 0x1ec1fdefdc000000

def z291 : W := mkw 0x090000040804214a 0x04800002040210a5 0xaa00472c780fe33e 0x550023963c07f19f

def z292 : W := mkw 0x3e259afda4b69fe5 0x1f12cd7ed25b4ff2 0x7da3baffa4729fe7 0xbed1dd7fd2394ff3

def z293 : W := mkw 0xf83fffff77ffdbc1 0xfc1fffffbbffede0 0xffffffffffffffc1 0xffffffffffffffe0

def z294 : W := mkw 0x06008051a0100ca5 0x03004028d0080652 0x300000d3a0001ce7 0x18000069d0000e73

def z295 : W := mkw 0xdc3eecfec7df1ff0 0x6e1f767f63ef8ff8 0xfffffcffc7ff1ff9 0xfffffe7fe3ff8ffc

def z296 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xc15c38c387831f39 0x60ae1c61c3c18f9c

def z297 : W := mkw 0x29011a040c26a14a 0x14808d02061350a5 0xffa3ff3c7c7fe3ff 0xffd1ff9e3e3ff1ff

def z298 : W := mkw 0x090480ff7804214b 0x8482407fbc0210a5 0xfe8047fff80fe3ff 0xff4023fffc07f1ff

def z299 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x291fbfc3f8000000 0x148fdfe1fc000000

def z300 : W := mkw 0xf03ffff807fbda80 0x781ffffc03fded40 0x017fb8c007f01c00 0x00bfdc6003f80e00

def z301 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x3da3bad3a4701c00 0x1ed1dd69d2380e00

def z302 : W := mkw 0x100c24a240801200 0x0806125120400900 0xfbdc3ce3c7801f01 0x7dee1e71e3c00f80

def z303 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xffdc7fe3c78fff39 0xffee3ff1e3c7ff9c

def z304 : W := mkw 0xe41b7f00876bc420 0x720dbf8043b5e210 0xffffffc387fffc21 0xffffffe1c3fffe10

def z305 : W := mkw 0x601b7f000523c000 0x300dbf800291e000 0x0f9fff000003e000 0x07cfff800001f000

def z306 : W := mkw 0x0400080084020420 0x0200040042010210 0x7d803ad3a4029ce7 0xbec01d69d2014e73

def z307 : W := mkw 0xdc3eecfec7df1ff0 0x6e1f767f63ef8ff8 0xd7fff8ff87fc1fc1 0xebfffc7fc3fe0fe0

def z308 : W := mkw 0x0f008055a8142def 0x0780402ad40a16f7 0xfe8047fff80fffff 0xff4023fffc07ffff

def z309 : W := mkw 0xe90008040f6fe14a 0x7480040207b7f0a5 0xfee0473c7fffe3ff 0xff70239e3ffff1ff

def z310 : W := mkw 0x0000000000000000 0x0000000000000000 0x30000010200000e7 0x1800000810000073

def z311 : W := mkw 0x090000040804214a 0x04800002040210a5 0x0000001c380000c6 0x0000000e1c000063

def z312 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e80470000000000 0x0740238000000000

def z313 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xffffc2fc27fe9fe7 0xffffe17e13ff4ff3

def z314 : W := mkw 0x0000805000100880 0x0000402800080440 0x100000d000001cc1 0x0800006800000e60

def z315 : W := mkw 0xc91a65040b4d614a 0x648d328205a6b0a5 0xfedc473c7b8fe3ff 0xff6e239e3dc7f1ff

def z316 : W := mkw 0xe0082c00076bc000 0x7004160003b5e000 0xcbfc3c0007ffe000 0xe5fe1e0003fff000

def z317 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z318 : W := mkw 0x001f77ab70000001 0x800fbbd5b8000000 0x2a1c7f2ff8000000 0x150e3f97fc000000

def z319 : W := mkw 0x001b770000000000 0x000dbb8000000000 0x011fb80000000000 0x008fdc0000000000

def z320 : W := mkw 0xbe219a55a6fe9fe5 0x5f10cd2ad37f4ff2 0xfde3bad3a7fe9fe7 0xfef1dd69d3ff4ff3

def z321 : W := mkw 0x091ff7ff7804214b 0x848ffbffbc0210a5 0x3f9ffffff80ce0c6 0x9fcffffffc067063

def z322 : W := mkw 0x4000080005030000 0x2000040002818000 0xc040000007830000 0x6020000003c18000

def z323 : W := mkw 0xa213d3512278c885 0x5109e9a8913c6442 0x0423c310207ce0c6 0x8211e188103e7063

def z324 : W := mkw 0x0000000000000000 0x0000000000000000 0x3c80021020000000 0x1e40010810000000

def z325 : W := mkw 0x0000000000000000 0x0000000000000000 0xc3dc000007800000 0x61ee000003c00000

def z326 : W := mkw 0xfe3ffeffe7ff9ff5 0x7f1fff7ff3ffcffa 0xfffffeffe7ff9fff 0xffffff7ff3ffcfff

def z327 : W := mkw 0x2f011a05ac26a56f 0x17808d02d61352b7 0xfe807f3ff80fe3ff 0xff403f9ffc07f1ff

def z328 : W := mkw 0x5c2cacfec5971ff0 0x2e16567f62cb8ff8 0xfbdc3cffc7831ff9 0x7dee1e7fe3c18ffc

def z329 : W := mkw 0x0008240240000000 0x0004120120000000 0x28003c03c0000000 0x14001e01e0000000

def z330 : W := mkw 0xd83e65ac03cd5340 0x6c1f32d601e6a9a0 0x825c452c038d6300 0x412e229601c6b180

def z331 : W := mkw 0x9836c0fc02cc1340 0x4c1b607e016609a0 0x97dfc0fc038c0300 0x4befe07e01c60180

def z332 : W := mkw 0xc01a650003494000 0x600d328001a4a000 0xcedc4700038fe000 0xe76e238001c7f000

def z333 : W := mkw 0xf61ffff3e7fbdeb5 0x7b0ffff9f3fdef5a 0xfffffff3e7ffffff 0xfffffff9f3ffffff

def z334 : W := mkw 0x001ee5fb70000001 0x800f72fdb8000000 0x321c45fff8000000 0x190e22fffc000000

def z335 : W := mkw 0x001b770370000001 0x800dbb81b8000000 0x2f9fff03f8000000 0x17cfff81fc000000

def z336 : W := mkw 0x20011a0004228000 0x10008d0002114000 0x7da3ba10247280e7 0xbed1dd0812394073

def z337 : W := mkw 0xbe36c8fc86fe9fe4 0x5f1b647e437f4ff2 0xd7ffc0fc07fe9fe7 0xebffe07e03ff4ff3

def z338 : W := mkw 0x2600885084328ca4 0x1300442842194652 0x55a380d004729ce7 0xaad1c06802394e73

def z339 : W := mkw 0xfd1f7fa6cfeff77a 0x7e8fbfd367f7fbbd 0xffffffffffffffff 0xffffffffffffffff

def z340 : W := mkw 0x64093f02c523c430 0x32049f816291e218 0x28003f03c003e038 0x14001f81e001f01c

def z341 : W := mkw 0x2000080004228000 0x1000040002114000 0x4020000004728000 0xa010000002394000

def z342 : W := mkw 0x0013530000000000 0x0009a98000000000 0x0403c30000000000 0x0201e18000000000

def z343 : W := mkw 0xbe37dafda6fe9fe5 0x5f1bed7ed37f4ff2 0xfffffaffa7fe9fe7 0xfffffd7fd3ff4ff3

def z344 : W := mkw 0x540c24a2c1811630 0x2a06125160c08b18 0xb25c04e3c3811f39 0x592e0271e1c08f9c

def z345 : W := mkw 0x090000040804214a 0x04800002040210a5 0xce80471c380fe0c6 0xe740238e1c07f063

def z346 : W := mkw 0x0000000000100880 0x0000000000080440 0x4020000004701cc1 0xa010000002380e60

def z347 : W := mkw 0x090000040804214a 0x04800002040210a5 0x8600473c780de3de 0xc300239e3c06f1ef

def z348 : W := mkw 0xaa33d25d227c89c5 0x5519e92e913e44e2 0x0423c21c207c80c6 0x8211e10e103e4063

def z349 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe80473c78030339 0x7f40239e3c01819c

def z350 : W := mkw 0x0816c0fc00040140 0x040b607e000200a0 0xd79fc0fc000c03c1 0xebcfe07e000601e0

def z351 : W := mkw 0x0000000000000000 0x0000000000000000 0x7e80473c780280e7 0xbf40239e3c014073

def z352 : W := mkw 0x2201120120208005 0x1100890090104002 0x0000020020008006 0x0000010010004003

def z353 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0x295c3cc3c7831c38 0x14ae1e61e3c18e1c

def z354 : W := mkw 0x20019a5004328880 0x1000cd2802194440 0x5da3bad004729cc1 0xaed1dd6802394e60

def z355 : W := mkw 0x9837d2fd22dc1bc1 0x4c1be97e916e0de0 0xfffffaffa7fc1fc1 0xfffffd7fd3fe0fe0

def z356 : W := mkw 0x5000000001811210 0x2800000000c08908 0x8040000003810318 0x4020000001c0818c

def z357 : W := mkw 0x8016c0f802480000 0x400b607c01240000 0xd7ffc0fc07fc0000 0xebffe07e03fe0000

def z358 : W := mkw 0xfe3ffffda7ffdfe5 0x7f1ffffed3ffeff2 0xffffffffa7ffffe7 0xffffffffd3fffff3

def z359 : W := mkw 0x26011a01a4228425 0x13008d00d2114212 0x0000380380000000 0x00001c01c0000000

def z360 : W := mkw 0x0009370370000001 0x80049b81b8000000 0x0000380380000000 0x00001c01c0000000

def z361 : W := mkw 0x091b77040804214a 0x048dbb82040210a5 0xff9fff3c780fe3ff 0xffcfff9e3c07f1ff

def z362 : W := mkw 0x001ee4fa40000000 0x000f727d20000000 0x3f9ffcffc0000000 0x1fcffe7fe0000000

def z363 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xffdc7fffff831f39 0x7fee3fffffc18f9c

def z364 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x3123b8d3a4701ce7 0x1891dc69d2380e73

def z365 : W := mkw 0x090000040804214a 0x04800002040210a5 0x3800073c7803e3ff 0x1c00039e3c01f1ff

def z366 : W := mkw 0x2201925120308885 0x1100c92890184442 0x3da3bad3a07080c6 0x9ed1dd69d0384063

def z367 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x55a3b8d384701cc1 0xaad1dc69c2380e60

def z368 : W := mkw 0x182480fc00941bc0 0x0c12407e004a0de0 0xd3dc00fc07801fc1 0x69ee007e03c00fe0

def z369 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xffffff1027ffe0e7 0xffffff8813fff073

def z370 : W := mkw 0x440c2ca2c5030430 0x2206165162818218 0x3b9c3ce3c0030038 0x1dce1e71e001801c

def z371 : W := mkw 0x27019a51ac32acaf 0x1380cd28d6195657 0x7da3bfd3fc73fcff 0xbed1dfe9fe39fe7f

def z372 : W := mkw 0x550c2ca2cd83363a 0x2a86165166c19b1d 0xfbdc3fe3ff83ff3f 0x7dee1ff1ffc1ff9f

def z373 : W := mkw 0x0016c0f800100880 0x000b607c00080440 0x57bfc0fc04701cc1 0xabdfe07e02380e60

def z374 : W := mkw 0x140400a2c0801630 0x0a02005160400b18 0x000000c380001c00 0x00000061c0000e00

def z375 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0xc7ffc0c007fc1c00 0xe3ffe06003fe0e00

def z376 : W := mkw 0x000400a000000000 0x0002005000000000 0x139c00e000000000 0x09ce007000000000

def z377 : W := mkw 0xbe37dafda6fe9fe5 0x5f1bed7ed37f4ff2 0xd7fff8ff87fc1fc1 0xebfffc7fc3fe0fe0

def z378 : W := mkw 0x010000000800200a 0x0080000004001005 0x200000007800003e 0x100000003c00001f

def z379 : W := mkw 0x140400a2c0801630 0x0a02005160400b18 0xfa8004e3c0031f39 0x7d400271e0018f9c

def z380 : W := mkw 0x0800000400040140 0x04000002000200a0 0xfe80443c400f03f9 0xff40221e200781fc

def z381 : W := mkw 0xa00000000268c000 0x5000000001346000 0x00200000007ce000 0x80100000003e7000

def z382 : W := mkw 0x66093e03e5238435 0x33049f01f291c21a 0x28003e03e003803e 0x14001f01f001c01f

def z383 : W := mkw 0x983ee5fe52dc1bc0 0xcc1f72ff296e0de0 0xd7ffc5fc5ffc1fc1 0xebffe2fe2ffe0fe0

def z384 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0x8a5c7f00038fe000 0x452e3f8001c7f000

def z385 : W := mkw 0x001f77a240000000 0x000fbbd120000000 0x3f9fffe3c0000000 0x1fcffff1e0000000

def z386 : W := mkw 0x0600000080100ca4 0x0300000040080652 0x0000000000001ce7 0x0000000000000e73

def z387 : W := mkw 0x261ffffbf4328ca5 0x930ffffdfa194652 0x013fb8c384701c00 0x009fdc61c2380e00

def z388 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0x315c38e3c7801f39 0x18ae1c71e3c00f9c

def z389 : W := mkw 0x010937037800200b 0x80849b81bc001005 0x28003f03f803e03e 0x14001f81fc01f01f

def z390 : W := mkw 0xc01e65aa53494000 0xe00f32d529a4a000 0x825c452c5b8d6000 0x412e22962dc6b000

def z391 : W := mkw 0x541ffffbf5831631 0xaa0ffffdfac18b18 0xfbdfbce3c7831f39 0x7defde71e3c18f9c

def z392 : W := mkw 0xe01bff59376bc001 0xf00dffac9bb5e000 0xcfffff1c3fffe000 0xe7ffff8e1ffff000

def z393 : W := mkw 0x0000000000000000 0x0000000000000000 0x2800020020028026 0x1400010010014013

def z394 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x179ff8ff80000000 0x0bcffc7fc0000000

def z395 : W := mkw 0x091e65ae5804214a 0x848f32d72c0210a5 0xfe9c473c780fe3ff 0xff4e239e3c07f1ff

def z396 : W := mkw 0x1e2480fda0941fe5 0x0f12407ed04a0ff2 0x300000ffa0001fe7 0x1800007fd0000ff3

def z397 : W := mkw 0x8012400002480000 0x4009200001240000 0x825c4000038c0000 0x412e200001c60000

def z398 : W := mkw 0x192480fc08943bca 0x0c92407e044a1de5 0xfe8047fc780fffff 0xff4023fe3c07ffff

def z399 : W := mkw 0xa01353000268c000 0x5009a98001346000 0xc7ffc30007fce000 0xe3ffe18003fe7000

def z400 : W := mkw 0x540dbef3e5831631 0x2a06df79f2c18b18 0xffdfbef3e7831f39 0x7fefdf79f3c18f9c

def z401 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x4423821024729ce7 0xa211c10812394e73

def z402 : W := mkw 0x1d0400a6c884377a 0x0e82005364421bbd 0xfe8047fff80fffff 0xff4023fffc07ffff

def z403 : W := mkw 0x201b7f0004228000 0x100dbf8002114000 0x4fbfff0004728000 0xa7dfff8002394000

def z404 : W := mkw 0x2600080084228424 0x1300040042114212 0x0000000000028026 0x0000000000014013

def z405 : W := mkw 0x501e65aa51811210 0xa80f32d528c08908 0x825c452c5b810318 0x412e22962dc0818c

def z406 : W := mkw 0x011ff7fb7800200b 0x808ffbfdbc001005 0x3f9ffffff803e03e 0x1fcffffffc01f01f

def z407 : W := mkw 0xf03ffff807fbda80 0x781ffffc03fded40 0xcfffffc007fffc00 0xe7ffffe003fffe00

def z408 : W := mkw 0x090000040804214a 0x04800002040210a5 0xb200453c780d63ff 0x5900229e3c06b1ff

def z409 : W := mkw 0x2600080084328ca4 0x1300040042194652 0x79a038c384729ce7 0xbcd01c61c2394e73

def z410 : W := mkw 0xd43eecfac7db1eb0 0x6a1f767d63ed8f58 0xfbffbce3c7f31f39 0x7dffde71e3f98f9c

def z411 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x3b9fbce3c0000000 0x1dcfde71e0000000

def z412 : W := mkw 0x010000000800200a 0x0080000004001005 0xee804700780fe03e 0xf74023803c07f01f

def z413 : W := mkw 0xe0011a00076bc000 0x70008d0003b5e000 0xcde3ba0007ffe000 0xe6f1dd0003fff000

def z414 : W := mkw 0x090000040804214a 0x04800002040210a5 0xc400431c380fe3ff 0xe200218e1c07f1ff

def z415 : W := mkw 0x000db6f360000001 0x0006db79b0000000 0x3f9fbef3e0000000 0x1fcfdf79f0000000

def z416 : W := mkw 0x0916c0fc0804214a 0x048b607e040210a5 0xff9fc7fc780fe3ff 0xffcfe3fe3c07f1ff

def z417 : W := mkw 0x06019251a0100ca5 0x0300c928d0080652 0x3d83bad3a0001ce7 0x1ec1dd69d0000e73

def z418 : W := mkw 0x0000805000100880 0x0000402800080440 0x04238010007000c0 0x8211c00800380060

def z419 : W := mkw 0x500c24a241811210 0x2806125120c08908 0x005c000003800000 0x002e000001c00000

def z420 : W := mkw 0x000400a240000000 0x0002005120000000 0x300000e3c0000000 0x18000071e0000000

def z421 : W := mkw 0x20011a0004228000 0x10008d0002114000 0x08003a0000028000 0x04001d0000014000

def z422 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xaa5c3c23c3830338 0x552e1e11e1c1819c

def z423 : W := mkw 0xa613da51a67a8ca5 0x5309ed28d33d4652 0xfffffad3a7fe9ce7 0xfffffd69d3ff4e73

def z424 : W := mkw 0x060480fbf0100ca5 0x8302407df8080652 0x300000fff8001ce7 0x1800007ffc000e73

def z425 : W := mkw 0x27011a01ac22a42f 0x13808d00d6115217 0x28003f03f803e03e 0x14001f81fc01f01f

def z426 : W := mkw 0xe91b7f040f6fe14a 0x748dbf8207b7f0a5 0xcfffff2c5fffe318 0xe7ffff962ffff18c

def z427 : W := mkw 0x760dbef3e5b39eb5 0x3b06df79f2d9cf5a 0xfbffbce3c7f31f39 0x7dffde71e3f98f9c

def z428 : W := mkw 0x160480f3e0901eb5 0x0b024079f0480f5a 0x300000f3e0001fff 0x18000079f0000fff

def z429 : W := mkw 0xe41b7f02c76bc430 0x720dbf8163b5e218 0xefffff03c7ffe038 0xf7ffff81e3fff01c

def z430 : W := mkw 0x60093f000523c000 0x30049f800291e000 0x0000380000000000 0x00001c0000000000

def z431 : W := mkw 0x0009b75370000001 0x8004dba9b8000000 0x3d83bfd3f8000000 0x1ec1dfe9fc000000

def z432 : W := mkw 0x901640a002c81200 0x480b205001640900 0xd7ffc0e007fc1f01 0xebffe07003fe0f80

def z433 : W := mkw 0x090000040804214a 0x04800002040210a5 0xfa80043c780303ff 0x7d40021e3c0181ff

def z434 : W := mkw 0xe01ffffb776bc001 0xf00ffffdbbb5e000 0xcfffffc387ffe000 0xe7ffffe1c3fff000

def z435 : W := mkw 0x60093f037523c001 0xb0049f81ba91e000 0x28003f03f803e000 0x14001f81fc01f000

def z436 : W := mkw 0x000592fb70000001 0x8002c97db8000000 0x3d83bafff8000000 0x1ec1dd7ffc000000

def z437 : W := mkw 0x24011a0084228420 0x12008d0042114210 0x7da3bac384729c21 0xbed1dd61c2394e10

def z438 : W := mkw 0x4400080085030430 0x2200040042818218 0x0000000000030038 0x000000000001801c

def z439 : W := mkw 0x5c0c2ca6c5871770 0x2e06165362c38bb8 0xffdc7cffc78f1ff9 0xffee3e7fe3c78ffc

def z440 : W := mkw 0x090000040804214a 0x04800002040210a5 0x3e80473c780ce0c6 0x9f40239e3c067063

def z441 : W := mkw 0x090000040804214a 0x04800002040210a5 0x00000000000ce0c6 0x8000000000067063

def z442 : W := mkw 0x000c24a240000000 0x0006125120000000 0x021c042040000000 0x010e021020000000

def z443 : W := mkw 0xb637daf9a6fa9ea5 0x5b1bed7cd37d4f52 0x017fb8c387f01c00 0x00bfdc61c3f80e00

def z444 : W := mkw 0x541f7fa2c5831630 0x2a0fbfd162c18b18 0xffdfffe3c7831f39 0x7feffff1e3c18f9c

def z445 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x79a3b8c384721c21 0x3cd1dc61c2390e10

def z446 : W := mkw 0x081ff7ff70040141 0x840ffbffb80200a0 0xff9ffffff80c03c1 0xffcffffffc0601e0

def z447 : W := mkw 0xe01a6d00076bc000 0x700d368003b5e000 0xc27c450007ffe000 0xe13e228003fff000

def z448 : W := mkw 0x0008250250000000 0x8004128128000000 0x0000050058000000 0x000002802c000000

def z449 : W := mkw 0xe81b7f04076fc140 0x740dbf8203b7e0a0 0xdfffff3c07ffe3c1 0xefffff9e03fff1e0

def z450 : W := mkw 0xa833d35c027cc9c0 0x5419e9ae013e64e0 0x0423c31c007ce0c0 0x8211e18e003e7060

def z451 : W := mkw 0xbf37dafdaefebfef 0x5f9bed7ed77f5ff7 0xffffffffffffffff 0xffffffffffffffff

def z452 : W := mkw 0x192480fc08943bca 0x0c92407e044a1de5 0x300000fc78001fff 0x1800007e3c000fff

def z453 : W := mkw 0x69093f040d27e14a 0x34849f820693f0a5 0xfe807f3c780fe3ff 0xff403f9e3c07f1ff

def z454 : W := mkw 0x09008054081429ca 0x0480402a040a14e5 0xffa3c7fc7c7fffff 0xffd1e3fe3e3fffff

def z455 : W := mkw 0x04000002c0000430 0x0200000160000218 0x20000003c0000038 0x10000001e000001c

def z456 : W := mkw 0x740d3ea2c5a39630 0x3a069f5162d1cb18 0xffffbee3c7f39f39 0xffffdf71e3f9cf9c

def z457 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe804710200fe0e7 0xff4023881007f073

def z458 : W := mkw 0xa01b77000268c000 0x500dbb8001346000 0x0fbfff00007ce000 0x87dfff80003e7000

def z459 : W := mkw 0x26011a01a4328ca5 0x13008d00d2194652 0x68203a03a4729ce7 0xb4101d01d2394e73

def z460 : W := mkw 0x0001925120000001 0x0000c92890000000 0x0103b8c380000000 0x0081dc61c0000000

def z461 : W := mkw 0x0001925120100881 0x0000c92890080440 0x7da3bad3a4701cc1 0xbed1dd69d2380e60

def z462 : W := mkw 0x090000040804214a 0x04800002040210a5 0xd680403c000fe3ff 0xeb40201e0007f1ff

def z463 : W := mkw 0x8832c05c025c09c0 0x4419602e012e04e0 0xc7ffc01c07fc00c0 0xe3ffe00e03fe0060

def z464 : W := mkw 0x140400a2c0801630 0x0a02005160400b18 0xf3dc00e3c7801f39 0x79ee0071e3c00f9c

def z465 : W := mkw 0x001b770000000000 0x000dbb8000000000 0xcf9fff00000fe000 0xe7cfff800007f000

def z466 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xd7ffc0fc07ffffff 0xebffe07e03ffffff

def z467 : W := mkw 0x0012c05800000000 0x0009602c00000000 0x0403c01c00000000 0x0201e00e00000000

def z468 : W := mkw 0xa91353040a6ce14a 0x5489a982053670a5 0x0423c31c387ce0c6 0x8211e18e1c3e7063

def z469 : W := mkw 0x100400a000801200 0x0802005000400900 0x100000e000001f01 0x0800007000000f80

def z470 : W := mkw 0x090000040804214a 0x04800002040210a5 0xfc800210200fe3ff 0xfe4001081007f1ff

def z471 : W := mkw 0x4008240241010010 0x2004120120808008 0x0000040040010018 0x000002002000800c

def z472 : W := mkw 0x010000000800200a 0x0080000004001005 0x7c8007107803e0ff 0xbe4003883c01f07f

def z473 : W := mkw 0xb837dafc06fe9bc0 0x5c1bed7e037f4de0 0xdffffafc07fe9fc1 0xeffffd7e03ff4fe0

def z474 : W := mkw 0x6609bf51a533cca5 0x3304dfa8d299e652 0x7da3bfd3a473fce7 0xbed1dfe9d239fe73

def z475 : W := mkw 0xc000000003494000 0x6000000001a4a000 0x80400000038d6000 0x4020000001c6b000

def z476 : W := mkw 0x0820805c001409c0 0x0410402e000a04e0 0x0000001c000000c0 0x0000000e00000060

def z477 : W := mkw 0x090000040804214a 0x04800002040210a5 0xc200452c580fe3ff 0xe10022962c07f1ff

def z478 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0x79dc38c387821c21 0x3cee1c61c3c10e10

def z479 : W := mkw 0x001ee5fa50000000 0x800f72fd28000000 0x179fc5fc58000000 0x0bcfe2fe2c000000

def z480 : W := mkw 0xfc3ffffec7ffdff0 0x7e1fffff63ffeff8 0xffffffffc7fffff9 0xffffffffe3fffffc

def z481 : W := mkw 0x000c24a240000000 0x0006125120000000 0x011c38c380000000 0x008e1c61c0000000

def z482 : W := mkw 0x001f77aa50000000 0x800fbbd528000000 0x0f9fff2c58000000 0x07cfff962c000000

def z483 : W := mkw 0x090000040804214a 0x04800002040210a5 0xe8000700780fe3ff 0xf40003803c07f1ff

def z484 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0x867fc03c03fc03c0 0xc33fe01e01fe01e0

def z485 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x2c23ba13a07280e6 0x9611dd09d0394073

def z486 : W := mkw 0x0016c0f800000000 0x000b607c00000000 0x011f80c000000000 0x008fc06000000000

def z487 : W := mkw 0x740d3fa2c5a3d630 0x3a069fd162d1eb18 0xfbdc3fe3c783ff39 0x7dee1ff1e3c1ff9c

def z488 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x17ffc0fc07f01c00 0x0bffe07e03f80e00

def z489 : W := mkw 0x0800000400040140 0x04000002000200a0 0x1000003c000003c1 0x0800001e000001e0

def z490 : W := mkw 0x001e65aa50000000 0x800f32d528000000 0x3b9c7defd8000000 0x1dce3ef7ec000000

def z491 : W := mkw 0x0200805120100885 0x0100402890080442 0x00000010200000c6 0x0000000810000063

def z492 : W := mkw 0x26011a01a4228425 0x13008d00d2114212 0x79803ac3a4029c27 0x3cc01d61d2014e13

def z493 : W := mkw 0x091e65ae5804214a 0x848f32d72c0210a5 0x821c452c580d6318 0x410e22962c06b18c

def z494 : W := mkw 0xe91b7f040f6fe14a 0x748dbf8207b7f0a5 0xcfffff0007ffe3ff 0xe7ffff8003fff1ff

def z495 : W := mkw 0xf41b7f0087ebd630 0x7a0dbf8043f5eb18 0xcfffff0007ffff39 0xe7ffff8003ffff9c

def z496 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x0f9fffc380000000 0x07cfffe1c0000000

def z497 : W := mkw 0x8000000002480000 0x4000000001240000 0xc060000007fc0000 0xe030000003fe0000

def z498 : W := mkw 0xf40c2ca2c7ebd630 0x7a06165163f5eb18 0xfbfc3ce3c7ffff39 0xfdfe1e71e3ffff9c

def z499 : W := mkw 0x0400080084020420 0x0200040042010210 0x010038c384001c00 0x00801c61c2000e00

def z500 : W := mkw 0x983640ac02cc1340 0x4c1b2056016609a0 0xd3dc40ec078c1f01 0x69ee207603c60f80

def z501 : W := mkw 0x983640ac02dc1bc0 0x4c1b2056016e0de0 0xc27c402c07fc1fc1 0xe13e201603fe0fe0

def z502 : W := mkw 0x993640ac0acc334a 0x4c9b2056056619a5 0xfedc473c7b8fe3ff 0xff6e239e3dc7f1ff

def z503 : W := mkw 0x49082c040d07214a 0x24841602068390a5 0xffdc7f3c7f8fe3ff 0xffee3f9e3fc7f1ff

def z504 : W := mkw 0x201ffffb74228001 0x900ffffdba114000 0x7fbffffffc728000 0xbfdffffffe394000

def z505 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0000000000fe000 0xe00000000007f000

def z506 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x3d9fbad3a0000000 0x1ecfdd69d0000000

def z507 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xc7fff80007fc0000 0xe3fffc0003fe0000

def z508 : W := mkw 0x0400000080000420 0x0200000040000210 0x300000c380001c21 0x18000061c0000e10

def z509 : W := mkw 0x540408a085831630 0x2a02045042c18b18 0xd3dc00e007831f39 0x69ee007003c18f9c

def z510 : W := mkw 0xef1bff55af7fedef 0x778dffaad7bff6f7 0xffffffffffffffff 0xffffffffffffffff

def z511 : W := mkw 0xe01bff50077bc880 0x700dffa803bde440 0xdfffffd007fffcc1 0xefffffe803fffe60

def z512 : W := mkw 0xa0135a00066a8000 0x5009ad0003354000 0xcffffa0007fe8000 0xe7fffd0003ff4000

def z513 : W := mkw 0x090000040804214a 0x04800002040210a5 0x80000000000d6318 0x400000000006b18c

def z514 : W := mkw 0x982400a402dc1bc0 0x4c120052016e0de0 0xd3fc00e007fc1fc1 0xe9fe007003fe0fe0

def z515 : W := mkw 0x010000000800200a 0x0080000004001005 0x0000050058016018 0x000002802c00b00c

def z516 : W := mkw 0xb837d3fc02fcdbc0 0x5c1be9fe017e6de0 0xd7ffc3fc07fcffc1 0xebffe1fe03fe7fe0

def z517 : W := mkw 0xe01bff51276bc001 0x700dffa893b5e000 0xffffffd3a7ffe000 0xffffffe9d3fff000

def z518 : W := mkw 0x0013d35930000001 0x8009e9ac98000000 0x0003800000000000 0x0001c00000000000

def z519 : W := mkw 0x000400aa50000000 0x8002005528000000 0x0000002c58000000 0x000000162c000000

def z520 : W := mkw 0x0000000370000001 0x80000001b8000000 0x20000003f8000000 0x10000001fc000000

def z521 : W := mkw 0x0001925120000001 0x0000c92890000000 0x0403821020000000 0x0201c10810000000

def z522 : W := mkw 0xe61b7f00877bcca4 0x730dbf8043bde652 0xcfffff0007fffce7 0xe7ffff8003fffe73

def z523 : W := mkw 0x010000000800200a 0x0080000004001005 0x000003003800e006 0x000001801c007003

def z524 : W := mkw 0x44082c02c5030430 0x2204160162818218 0xfa803c23c0030339 0x7d401e11e001819c

def z525 : W := mkw 0x0800000400040140 0x04000002000200a0 0xde80473c000fe3c1 0xef40239e0007f1e0

def z526 : W := mkw 0x8012400002480000 0x4009200001240000 0x017f800007f00000 0x00bfc00003f80000

def z527 : W := mkw 0x2600080084328ca4 0x1300040042194652 0x7ca0021024729ce7 0xbe50010812394e73

def z528 : W := mkw 0x090c24a64804214a 0x04861253240210a5 0xff9c7ffff80fe3ff 0xffce3ffffc07f1ff

def z529 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xd7ffc3fc3ffcffc7 0xebffe1fe1ffe7fe3

def z530 : W := mkw 0x001e65aa50000000 0x800f32d528000000 0x001c000000000000 0x000e000000000000

def z531 : W := mkw 0x000480fb70000001 0x8002407db8000000 0x000000c380000000 0x00000061c0000000

def z532 : W := mkw 0x8836c0fc025c09c0 0x441b607e012e04e0 0x17bfc0fc007c00c0 0x8bdfe07e003e0060

def z533 : W := mkw 0x2f019a55ac36adef 0x1780cd2ad61b56f7 0x7da3bafffc729fff 0xbed1dd7ffe394fff

def z534 : W := mkw 0x26011a0084328ca4 0x13008d0042194652 0x4da3ba0004729ce7 0xa6d1dd0002394e73

def z535 : W := mkw 0x1836c0fc00941bc0 0x0c1b607e004a0de0 0x179fc0fc00001fc1 0x0bcfe07e00000fe0

def z536 : W := mkw 0xe6019a51a77bcca5 0x7300cd28d3bde652 0xfde3bad3a7fffce7 0xfef1dd69d3fffe73

def z537 : W := mkw 0x61093f000d23e00a 0x30849f800691f005 0x28003f007803e03e 0x14001f803c01f01f

def z538 : W := mkw 0x0800000400040140 0x04000002000200a0 0xfe80423c200e83e7 0xff40211e100741f3

def z539 : W := mkw 0xdc20080487df1ff0 0x6e10040243ef8ff8 0xc060000007ff1ff9 0xe030000003ff8ffc

def z540 : W := mkw 0x40082c0005030000 0x2004160002818000 0x08003c0000030000 0x04001e0000018000

def z541 : W := mkw 0x090480ff7804214b 0x8482407fbc0210a5 0x300000fff80003ff 0x1800007ffc0001ff

def z542 : W := mkw 0x983e65ae52cc1340 0xcc1f32d7296609a0 0x825c452c5b8c0300 0x412e22962dc60180

def z543 : W := mkw 0x88124004024c0140 0x44092002012600a0 0xd7ffc03c07fc03c1 0xebffe01e03fe01e0

def z544 : W := mkw 0x0000000000000000 0x0000000000000000 0x518000c004001c01 0x28c0006002000e00

def z545 : W := mkw 0x2b0192552834a9cf 0x1580c92a941a54e7 0xfea3c73c787fe3ff 0xff51e39e3c3ff1ff

def z546 : W := mkw 0xe0135b00076bc000 0x7009ad8003b5e000 0xc463c30007ffe000 0xe231e18003fff000

def z547 : W := mkw 0x44082c02c5030430 0x2204160162818218 0x79803cc3c4031c39 0x3cc01e61e2018e1c

def z548 : W := mkw 0x983640ac02cc1340 0x4c1b2056016609a0 0xc7ffc02c07fc0300 0xe3ffe01603fe0180

def z549 : W := mkw 0x0009370000000000 0x00049b8000000000 0x08003f0000000000 0x04001f8000000000

def z550 : W := mkw 0x090000040804214a 0x04800002040210a5 0xfa800420400fe3ff 0xfd4002102007f1ff

def z551 : W := mkw 0x982480fc02dc1bc0 0x4c12407e016e0de0 0xd06000fc07fc1fc1 0xe830007e03fe0fe0

def z552 : W := mkw 0x0016c0fb70000001 0x800b607db8000000 0x379fc0fff8000000 0x1bcfe07ffc000000

def z553 : W := mkw 0x182480fc00941bc0 0x0c12407e004a0de0 0x55a380fc04701fc1 0xaad1c07e02380fe0

def z554 : W := mkw 0x0000000000000000 0x0000000000000000 0x82004500000d6000 0x410022800006b000

def z555 : W := mkw 0xf93ffffc0ffffbca 0x7c9ffffe07fffde5 0xfffffffc7fffffff 0xfffffffe3fffffff

def z556 : W := mkw 0xd01e65a243c95210 0x680f32d121e4a908 0x825c4520438d6318 0x412e229021c6b18c

def z557 : W := mkw 0x541e6daad5831630 0xaa0f36d56ac18b18 0xfbdc7defdf831f39 0x7dee3ef7efc18f9c

def z558 : W := mkw 0xba37d2fd22fc9bc5 0x5d1be97e917e4de2 0xd7ffc2fc27fc9fc7 0xebffe17e13fe4fe3

def z559 : W := mkw 0x500c24a241811210 0x2806125120c08908 0xd3dc04e047811f19 0x69ee027023c08f8c

def z560 : W := mkw 0xf01f7fa007ebd200 0x780fbfd003f5e900 0xdfffffe007ffff01 0xeffffff003ffff80

def z561 : W := mkw 0x0400885084120ca0 0x0200442842090650 0x7da3b8d384721ce1 0xbed1dc69c2390e70

def z562 : W := mkw 0x0001925120000001 0x0000c92890000000 0x3f83fffff8000000 0x1fc1fffffc000000

def z563 : W := mkw 0x001b770000000000 0x000dbb8000000000 0x3f9fff3c78000000 0x1fcfff9e3c000000

def z564 : W := mkw 0x590c24a64985335a 0x2c86125324c299ad 0x825c452c5b8d6318 0x412e22962dc6b18c

def z565 : W := mkw 0xf83ffffc07ffdbc0 0x7c1ffffe03ffede0 0xd7fff8fc07fc1fc1 0xebfffc7e03fe0fe0

def z566 : W := mkw 0x60093f000523c000 0x30049f800291e000 0x4da3bf000473e000 0xa6d1df800239f000

def z567 : W := mkw 0xc01b770003494000 0x600dbb8001a4a000 0x8fdfff00038d6000 0x47efff8001c6b000

def z568 : W := mkw 0xe90008040f6fe14a 0x7480040207b7f0a5 0xc060000007ffe3ff 0xe030000003fff1ff

def z569 : W := mkw 0xf400080087ebd630 0x7a00040043f5eb18 0xc060000007ffff39 0xe030000003ffff9c

def z570 : W := mkw 0x0913d35d3804214b 0x8489e9ae9c0210a5 0xfe83c73c780fe3ff 0xff41e39e3c07f1ff

def z571 : W := mkw 0x0000080004020000 0x0000040002010000 0x4980380004020000 0x24c01c0002010000

def z572 : W := mkw 0xd83ee4fe43dd1bd0 0x6c1f727f21ee8de8 0xd7ffc4fc47fd1fd9 0xebffe27e23fe8fec

def z573 : W := mkw 0x1400000080801630 0x0a00000040400b18 0x0000000000001f39 0x0000000000000f9c

def z574 : W := mkw 0xe11b7f000f6be00a 0x708dbf8007b5f005 0xefffff007fffe03e 0xf7ffff803ffff01f

def z575 : W := mkw 0x760dbef3e5b39eb5 0x3b06df79f2d9cf5a 0x017fb8c387f01c00 0x00bfdc61c3f80e00

def z576 : W := mkw 0x9c36c0fec2dc1ff0 0x4e1b607f616e0ff8 0xf7ffc0ffc7fc1ff9 0xfbffe07fe3fe0ffc

def z577 : W := mkw 0x5400080085831630 0x2a00040042c18b18 0xf9c038c387831f39 0x7ce01c61c3c18f9c

def z578 : W := mkw 0x0800000400040140 0x04000002000200a0 0x8200402c000c0300 0x4100201600060180

def z579 : W := mkw 0x0400080084020420 0x0200040042010210 0x4000000004021c21 0x2000000002010e10

def z580 : W := mkw 0xe01ffffb776bc001 0xf00ffffdbbb5e000 0x3ffffffffff00000 0x1ffffffffff80000

def z581 : W := mkw 0x001bf75120000001 0x000dfba890000000 0x3f9fffd3a0000000 0x1fcfffe9d0000000

def z582 : W := mkw 0xd83e64ae43cd1350 0x6c1f325721e689a8 0x825c442c438d0318 0x412e221621c6818c

def z583 : W := mkw 0x401ffffb75030001 0xa00ffffdba818000 0xffdfffffff830000 0x7fefffffffc18000

def z584 : W := mkw 0x001ff7f800000000 0x000ffbfc00000000 0x1f9ffffc00000000 0x0fcffffe00000000

def z585 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xcbffbc0007f30000 0x65ffde0003f98000

def z586 : W := mkw 0xc91a65040b4d614a 0x648d328205a6b0a5 0x825c452c5b8d6318 0x412e22962dc6b18c

def z587 : W := mkw 0x100400a000801200 0x0802005000400900 0x825c002003800300 0x412e001001c00180

def z588 : W := mkw 0xe0000800076bc000 0x7000040003b5e000 0x0060000007f00000 0x0030000003f80000

def z589 : W := mkw 0x4008240001010000 0x2004120000808000 0x825c040003810000 0x412e020001c08000

def z590 : W := mkw 0x0000000000000000 0x0000000000000000 0x0200452c58000000 0x010022962c000000

def z591 : W := mkw 0xe01f7faa576bc000 0xf00fbfd52bb5e000 0xcfffff2c5fffe000 0xe7ffff962ffff000

def z592 : W := mkw 0x20011a0004228000 0x10008d0002114000 0x0123b80004700000 0x0091dc0002380000

def z593 : W := mkw 0xe6000800877bcca4 0x7300040043bde652 0xc060000007fffce7 0xe030000003fffe73

def z594 : W := mkw 0xa613db51a67acca5 0x5309eda8d33d6652 0x7da3fbd3a47efce7 0xbed1fde9d23f7e73

def z595 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000003c78000000 0x1800001e3c000000

def z596 : W := mkw 0x54082c0085831630 0x2a04160042c18b18 0xcbdc3c0007831f39 0x65ee1e0003c18f9c

def z597 : W := mkw 0x8032c05802580880 0x4019602c012c0440 0x0023800000700000 0x0011c00000380000

def z598 : W := mkw 0xb637daf9a6fa9ea5 0x5b1bed7cd37d4f52 0x7dffbad3a7f29ce7 0xbeffdd69d3f94e73

def z599 : W := mkw 0x0d0008048c06256a 0x06800402460312b5 0xff807ffffc0fffff 0xffc03ffffe07ffff

def z600 : W := mkw 0x001a650000000000 0x000d328000000000 0x021c450000000000 0x010e228000000000

def z601 : W := mkw 0x20019a5124228001 0x1000cd2892114000 0x7da3bad3a4728000 0xbed1dd69d2394000

def z602 : W := mkw 0x091ff7ff7804214b 0x848ffbffbc0210a5 0x3f9ffffff80003ff 0x1fcffffffc0001ff

def z603 : W := mkw 0x04019a51a4020421 0x0200cd28d2010210 0x7d83bad3a4021c21 0x3ec1dd69d2010e10

def z604 : W := mkw 0x200113000020c000 0x1000898000106000 0x000003000000e000 0x0000018000007000

def z605 : W := mkw 0x6609be53e5338cb5 0x3304df29f299c65a 0x7da3bed3e4739cff 0xbed1df69f239ce7f

def z606 : W := mkw 0x1820000400941bc0 0x0c100002004a0de0 0x0000000000001fc1 0x0000000000000fe0

def z607 : W := mkw 0x7f0dbef7edb7bfff 0x3f86df7bf6dbdfff 0xffffffffffffffff 0xffffffffffffffff

def z608 : W := mkw 0x0000805120000001 0x0000402890000000 0x300000d3a0000000 0x18000069d0000000

def z609 : W := mkw 0x0013d35930000001 0x8009e9ac98000000 0x3e83c73c78000000 0x1f41e39e3c000000

def z610 : W := mkw 0x0001120120000001 0x0000890090000000 0x28003a03a0000000 0x14001d01d0000000

def z611 : W := mkw 0x0400080084020420 0x0200040042010210 0xfb803ce3c4031f39 0x7dc01e71e2018f9c

def z612 : W := mkw 0x40082c0005030000 0x2004160002818000 0xfbdc3c2047830339 0x7dee1e1023c1819c

def z613 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0x0c23ff00007fe000 0x8611ff80003ff000

def z614 : W := mkw 0x5400080085831630 0x2a00040042c18b18 0xfac0042047831f39 0x7d60021023c18f9c

def z615 : W := mkw 0x0000000000000000 0x0000000000000000 0x04004300000ce000 0x8200218000067000

def z616 : W := mkw 0xae33da5da67e8de5 0x5719ed2ed33f46f2 0x7da3fadfa47e9ce7 0xbed1fd6fd23f4e73

def z617 : W := mkw 0x36059af3e4b29eb5 0x1b02cd79f2594f5a 0x7da3baf3e4729fff 0xbed1dd79f2394fff

def z618 : W := mkw 0x983ff7fc02dc1bc0 0x4c1ffbfe016e0de0 0xdffffffc07fc1fc1 0xeffffffe03fe0fe0

def z619 : W := mkw 0x2b0192552834a9cf 0x1580c92a941a54e7 0x0423c31c387ce0c6 0x8211e18e1c3e7063

def z620 : W := mkw 0x8832c05c025c09c0 0x4419602e012e04e0 0xd6a3c03c007c03c1 0xeb51e01e003e01e0

def z621 : W := mkw 0x182400ac00841340 0x0c120056004209a0 0x0000002c00000300 0x0000001600000180

def z622 : W := mkw 0x500c2ca005831200 0x2806165002c18900 0xdbdc3ce007831f01 0x6dee1e7003c18f80

def z623 : W := mkw 0xe0000800076bc000 0x7000040003b5e000 0xcee0470007ffe000 0xe770238003fff000

def z624 : W := mkw 0x000d37a370000001 0x80069bd1b8000000 0x3b9c3fe3f8000000 0x1dce1ff1fc000000

def z625 : W := mkw 0x001e65aa50000000 0x800f32d528000000 0x3e9c473c78000000 0x1f4e239e3c000000

def z626 : W := mkw 0x2600080084328ca4 0x1300040042194652 0x0020000004701c00 0x0010000002380e00

def z627 : W := mkw 0x9820000402cc1340 0x4c100002016609a0 0x80400000038c0300 0x4020000001c60180

def z628 : W := mkw 0x9832c05c02dc1bc0 0x4c19602e016e0de0 0xc463c01c07fc1fc1 0xe231e00e03fe0fe0

def z629 : W := mkw 0x4008250001014000 0x200412800080a000 0x0000050000016000 0x000002800000b000

def z630 : W := mkw 0xf41f7fa2c7ebd630 0x7a0fbfd163f5eb18 0xfbffbce3c7f31f39 0x7dffde71e3f98f9c

def z631 : W := mkw 0xe01ffff8076bc000 0x700ffffc03b5e000 0xdffffffc07ffe000 0xeffffffe03fff000

def z632 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0x3bdc3ce3c7801c00 0x1dee1e71e3c00e00

def z633 : W := mkw 0x1d0400a6c884377a 0x0e82005364421bbd 0x300000fff8001fff 0x1800007ffc000fff

def z634 : W := mkw 0x090000040804214a 0x04800002040210a5 0x00000000000003ff 0x00000000000001ff

def z635 : W := mkw 0x9820805402dc1bc0 0x4c10402a016e0de0 0xd5e380d007fc1fc1 0xeaf1c06803fe0fe0

def z636 : W := mkw 0x5d0c2ca6cd87377a 0x2e86165366c39bbd 0xfbdc7defdf8f7f39 0x7dee3ef7efc7bf9c

def z637 : W := mkw 0x1c2480fec0941ff0 0x0e12407f604a0ff8 0x300000ffc0001ff9 0x1800007fe0000ffc

def z638 : W := mkw 0x26019251a0308ca5 0x1300c928d0184652 0x342382d3a0709ce7 0x9a11c169d0384e73

def z639 : W := mkw 0xa01353000268c000 0x5009a98001346000 0x0023800000700000 0x0011c00000380000

def z640 : W := mkw 0x100400a240801210 0x0802005120400908 0x0000002040000318 0x000000102000018c

def z641 : W := mkw 0x0017d2f920000001 0x000be97c90000000 0x3f9ffaffa0000000 0x1fcffd7fd0000000

def z642 : W := mkw 0x983ee4fe42dc1bc0 0x4c1f727f216e0de0 0xfffffcffc7fc1fc1 0xfffffe7fe3fe0fe0

def z643 : W := mkw 0x992000040adc3bca 0x4c900002056e1de5 0xc060000007ffffff 0xe030000003ffffff

def z644 : W := mkw 0x090000040804214a 0x04800002040210a5 0x7c80431c380ee0e7 0xbe40218e1c077073

def z645 : W := mkw 0xe21bff51277bc885 0x710dffa893bde442 0xcfffff1027ffe0c6 0xe7ffff8813fff063

def z646 : W := mkw 0x090000040804214a 0x04800002040210a5 0x3400433c780ce3ff 0x9a00219e3c0671ff

def z647 : W := mkw 0x891240040a4c214a 0x44892002052610a5 0xffffc73c7fffe3ff 0xffffe39e3ffff1ff

def z648 : W := mkw 0xe91fffff7f6fe14b 0xf48fffffbfb7f0a5 0xffffffffffffe3ff 0xfffffffffffff1ff

def z649 : W := mkw 0xf41ffffbf7ebd631 0xfa0ffffdfbf5eb18 0xffffffffffffff39 0xffffffffffffff9c

def z650 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0x4dffba0007f28000 0xa6ffdd0003f94000

def z651 : W := mkw 0x06008051a0100ca5 0x03004028d0080652 0x7c8002d3a0029ce7 0xbe400169d0014e73

def z652 : W := mkw 0x44082c0085030420 0x2204160042818210 0xfbdc3cc387831c21 0x7dee1e61c3c18e10

def z653 : W := mkw 0x4d082c06cd07257a 0x26841603668392bd 0xfe807f3ff80fe3ff 0xff403f9ffc07f1ff

def z654 : W := mkw 0x040c2ca2c4020420 0x0206165162010210 0x7b9c3ce3c4021c21 0x3dce1e71e2010e10

def z655 : W := mkw 0x540408a2c5831630 0x2a02045162c18b18 0xf04000e3c7831f39 0x78200071e3c18f9c

def z656 : W := mkw 0xe91b7f040f6fe14a 0x748dbf8207b7f0a5 0xcfffff1c3fffe0c6 0xe7ffff8e1ffff063

def z657 : W := mkw 0x0000000000000000 0x0000000000000000 0xc6804000000c0000 0xe340200000060000

def z658 : W := mkw 0xa91353040a6ce14a 0x5489a982053670a5 0xfea3c73c787fe3ff 0xff51e39e3c3ff1ff

def z659 : W := mkw 0x090000040804214a 0x04800002040210a5 0xbe80473c780d6318 0x5f40239e3c06b18c

def z660 : W := mkw 0x903ff7fb72d81a81 0xc81ffbfdb96c0d40 0x017fb8c387f01c00 0x00bfdc61c3f80e00

def z661 : W := mkw 0x26019a51a4228425 0x1300cd28d2114212 0x3d83bad3a0028026 0x1ec1dd69d0014013

def z662 : W := mkw 0x26059afbf4328ca5 0x9302cd7dfa194652 0x7da3bafffc729ce7 0xbed1dd7ffe394e73

def z663 : W := mkw 0x8012410002484000 0x4009208001242000 0x00004100000c6000 0x0000208000063000

def z664 : W := mkw 0xbe20080486fe9fe4 0x5f100402437f4ff2 0xc060000007fe9fe7 0xe030000003ff4ff3

def z665 : W := mkw 0x0012400000000000 0x0009200000000000 0x079fc00000000000 0x03cfe00000000000

def z666 : W := mkw 0xdc2c2ca6c7df1ff0 0x6e16165363ef8ff8 0xfbfc3ce3c7ff1ff9 0xfdfe1e71e3ff8ffc

def z667 : W := mkw 0x090000040804214a 0x04800002040210a5 0xce804700000fe3ff 0xe74023800007f1ff

def z668 : W := mkw 0xf41f7fa2c7ebd630 0x7a0fbfd163f5eb18 0x017fb8c387f01c00 0x00bfdc61c3f80e00

def z669 : W := mkw 0x001640a800000000 0x000b205400000000 0x021c402c00000000 0x010e201600000000

def z670 : W := mkw 0x540cacfbf5831631 0xaa06567dfac18b18 0xfbdc3cffff831f39 0x7dee1e7fffc18f9c

def z671 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe800630600383ff 0xff4003183001c1ff

def z672 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0x0fffff0007f00000 0x07ffff8003f80000

def z673 : W := mkw 0x2213d35930308885 0x9109e9ac98184442 0x0423c31c387080c6 0x8211e18e1c384063

def z674 : W := mkw 0x180400a400841340 0x0c020052004209a0 0xd7dc40fc078c1fc1 0xebee207e03c60fe0

def z675 : W := mkw 0x2e019a55a4368de5 0x1700cd2ad21b46f2 0xffa3faffa47e9fe7 0xffd1fd7fd23f4ff3

def z676 : W := mkw 0x140480fbf0801631 0x8a02407df8400b18 0x300000fff8001f39 0x1800007ffc000f9c

def z677 : W := mkw 0x090000040804214a 0x04800002040210a5 0x7c80023c780283ff 0xbe40011e3c0141ff

def z678 : W := mkw 0x06008051a0100ca5 0x03004028d0080652 0x75a380d3a4701ce7 0xbad1c069d2380e73

def z679 : W := mkw 0x761ffffbf5b39eb5 0xbb0ffffdfad9cf5a 0xfffffffffff39fff 0xfffffffffff9cfff

def z680 : W := mkw 0xe61ffffbf77bcca5 0xf30ffffdfbbde652 0xfffffffffffffce7 0xfffffffffffffe73

def z681 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xc25c042047831f39 0x612e021023c18f9c

def z682 : W := mkw 0xdc3ffffff7df1ff1 0xee1ffffffbef8ff8 0xffffffffffff1ff9 0xffffffffffff8ffc

def z683 : W := mkw 0x001bf75930000001 0x800dfbac98000000 0x0f9fff1c38000000 0x07cfff8e1c000000

def z684 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000000000030339 0x600000000001819c

def z685 : W := mkw 0xa0135b00066ac000 0x5009ad8003356000 0x4da3fb00047ee000 0xa6d1fd80023f7000

def z686 : W := mkw 0x0012410810000000 0x8009208408000000 0x0000410c18000000 0x000020860c000000

def z687 : W := mkw 0x2f019a55ac36adef 0x1780cd2ad61b56f7 0x7da3fbdfbc7efce7 0xbed1fdefde3f7e73

def z688 : W := mkw 0x441ffffbf5030431 0xa20ffffdfa818218 0x3f9ffffff8030038 0x1fcffffffc01801c

def z689 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400431c38000000 0x0200218e1c000000

def z690 : W := mkw 0x2200000000308884 0x1100000000184442 0x00200000007080c6 0x8010000000384063

def z691 : W := mkw 0x090000040804214a 0x04800002040210a5 0x0000410c180c6000 0x000020860c063000

def z692 : W := mkw 0x983640ac02cc1340 0x4c1b2056016609a0 0xd6dc403c038c03c1 0xeb6e201e01c601e0

def z693 : W := mkw 0x40082c0005030000 0x2004160002818000 0x015c380007800000 0x00ae1c0003c00000

def z694 : W := mkw 0xc01a6d00074b4000 0x600d368003a5a000 0xcbdc7d00078f6000 0x65ee3e8003c7b000

def z695 : W := mkw 0xe61bff51a77bcca5 0x730dffa8d3bde652 0x017fb8c387f01c00 0x00bfdc61c3f80e00

def z696 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0x1423c0fc007c1fc1 0x8a11e07e003e0fe0

def z697 : W := mkw 0x5400080085831630 0x2a00040042c18b18 0x0040000007801c00 0x0020000003c00e00

def z698 : W := mkw 0x541ffffbf5831631 0xaa0ffffdfac18b18 0x015fb8c387801c00 0x00afdc61c3c00e00

def z699 : W := mkw 0x06008051a0100ca5 0x03004028d0080652 0x000000c380001c00 0x00000061c0000e00

def z700 : W := mkw 0x2613db59b4328ca5 0x9309edacda194652 0x7da3fbdfbc729ce7 0xbed1fdefde394e73

def z701 : W := mkw 0x261ffffbf4328ca5 0x930ffffdfa194652 0x3fbffffffc701c00 0x1fdffffffe380e00

def z702 : W := mkw 0x0f008055a8142def 0x0780402ad40a16f7 0x300000fff8001fff 0x1800007ffc000fff

def z703 : W := mkw 0x26008851a4328ca5 0x13004428d2194652 0x702000d3a4729ce7 0xb8100069d2394e73

def z704 : W := mkw 0x560cacf3e5931eb5 0x2b065679f2c98f5a 0xfbdc3cf3e7831fff 0x7dee1e79f3c18fff

def z705 : W := mkw 0x0000000000000000 0x0000000000000000 0x2800070078000000 0x140003803c000000

def z706 : W := mkw 0x06008851a4120ca5 0x03004428d2090652 0x798038d3a4021ce7 0x3cc01c69d2010e73

def z707 : W := mkw 0x9829370772dc1bc1 0xcc149b83b96e0de0 0xe8603f03fffc1fc1 0xf4301f81fffe0fe0

def z708 : W := mkw 0x180480f400941bc0 0x0c02407a004a0de0 0xd7ffc0fc07fc1fc1 0xebffe07e03fe0fe0

def z709 : W := mkw 0x44082c0085030420 0x2204160042818210 0xfbdc3ce3c7831f39 0x7dee1e71e3c18f9c

def z710 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xfbdc3fe3c783ff39 0x7dee1ff1e3c1ff9c

def z711 : W := mkw 0x4d0008048d07257a 0x26800402468392bd 0xc0000000000fe3ff 0xe00000000007f1ff

def z712 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x4523bad3a4729ce7 0xa291dd69d2394e73

def z713 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x037fc0ec07f01c00 0x01bfe07603f80e00

def z714 : W := mkw 0xe61b7f03e76bc435 0x730dbf81f3b5e21a 0xefffff03e7ffe03e 0xf7ffff81f3fff01f

def z715 : W := mkw 0xc61ae551a3594ca5 0x630d72a8d1aca652 0xb25c45d3a38d7ce7 0x592e22e9d1c6be73

def z716 : W := mkw 0x803ff7fb72580881 0xc01ffbfdb92c0440 0x3fbffffff8700000 0x1fdffffffc380000

def z717 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0x015c38e3c7801f18 0x00ae1c71e3c00f8c

def z718 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xdfffc7fc5fffffd9 0xefffe3fe2fffffec

def z719 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xd7ffc0fc07fcffc7 0xebffe07e03fe7fe3

def z720 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x3f9ffffff80000e7 0x1fcffffffc000073

def z721 : W := mkw 0x903ff7fb72d81a81 0xc81ffbfdb96c0d40 0xfffffffffffc1c00 0xfffffffffffe0e00

def z722 : W := mkw 0xc01a6d00074b4000 0x600d368003a5a000 0xcffffd0007ff6000 0xe7fffe8003ffb000

def z723 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xd3ff80e007fc1fc1 0xe9ffc07003fe0fe0

def z724 : W := mkw 0x9832400402dc1bc0 0x4c192002016e0de0 0xd7ffc03c07fc1fc1 0xebffe01e03fe0fe0

def z725 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xc67fc70007ffe000 0xe33fe38003fff000

def z726 : W := mkw 0x64093f03f523c431 0xb2049f81fa91e218 0x28003f03f803e038 0x14001f81fc01f01c

def z727 : W := mkw 0x801ff7fb72480001 0xc00ffbfdb9240000 0xffffffffffffe000 0xfffffffffffff000

def z728 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x3f9ffffff803e000 0x1fcffffffc01f000

def z729 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x117f80d007f01cc1 0x08bfc06803f80e60

def z730 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0x17ffc0fc07f01fc1 0x0bffe07e03f80fe0

def z731 : W := mkw 0x001b770b70000001 0x800dbb85b8000000 0x28007f0ff8000000 0x14003f87fc000000

def z732 : W := mkw 0x182480fc00941bc0 0x0c12407e004a0de0 0xd7ff80fc07f01fc1 0xebffc07e03f80fe0

def z733 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xd7ffc0fc07ff1ff9 0xebffe07e03ff8ffc

def z734 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xffdc3cf3c7831ff9 0xffee1e79e3c18ffc

def z735 : W := mkw 0x0009370370000001 0x80049b81b8000000 0x38003f3ff8000000 0x1c001f9ffc000000

def z736 : W := mkw 0xa21ff7fb7278c885 0xd10ffbfdb93c6442 0x3fbffffff87ce0c6 0x9fdffffffc3e7063

def z737 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xffffc7fc7ffc1fff 0xffffe3fe3ffe0fff

def z738 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0x057fc3dc3ffcfcc6 0x82bfe1ee1ffe7e63

def z739 : W := mkw 0x8012400002480000 0x4009200001240000 0xc7ffc30007fce000 0xe3ffe18003fe7000

def z740 : W := mkw 0x64093f008523c430 0x32049f804291e218 0x08003f000003e038 0x04001f800001f01c

def z741 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x837fc0c007fc1c00 0x41bfe06003fe0e00

def z742 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xffffc7fc7ffe9fe7 0xffffe3fe3fff4ff3

def z743 : W := mkw 0x001ff7fb70100881 0x800ffbfdb8080440 0x3fbffffffc701c00 0x1fdffffffe380e00

def z744 : W := mkw 0x64093f02c523c430 0x32049f816291e218 0x0000380380000000 0x00001c01c0000000

def z745 : W := mkw 0x000db7fb70000001 0x8006dbfdb8000000 0x300038fff8000000 0x18001c7ffc000000

def z746 : W := mkw 0x8012c05002580880 0x40096028012c0440 0x017f80c007f01c00 0x00bfc06003f80e00

def z747 : W := mkw 0xe41b7f02c76bc430 0x720dbf8163b5e218 0xffffff23c7ffe339 0xffffff91e3fff19c

def z748 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xd7ffc5fc5fffffff 0xebffe2fe2fffffff

def z749 : W := mkw 0x261e6daad4328ca4 0x930f36d56a194652 0x423c452c5c729ce7 0xa11e22962e394e73

def z750 : W := mkw 0x000592fb70000001 0x8002c97db8000000 0x38003afff8000000 0x1c001d7ffc000000

def z751 : W := mkw 0x0009b75b70000001 0x8004dbadb8000000 0x28003f1ff8000000 0x14001f8ffc000000

def z752 : W := mkw 0xc01b770003494000 0x600dbb8001a4a000 0xcfffff0007fd6000 0xe7ffff8003feb000

def z753 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0x877fff0007fde000 0xc3bfff8003fef000

def z754 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0xbf9ffffff80d6000 0x5fcffffffc06b000

def z755 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0xff9ffffff8030000 0x7fcffffffc018000

def z756 : W := mkw 0x140408a084821620 0x0a02045042410b10 0xfbdc3ce3c7831f39 0x7dee1e71e3c18f9c

def z757 : W := mkw 0x64093f02c523c430 0x32049f816291e218 0xfe807f23c00fe339 0xff403f91e007f19c

def z758 : W := mkw 0xa01ff7fb7268c001 0xd00ffbfdb9346000 0xfffffffffffce000 0xfffffffffffe7000

def z759 : W := mkw 0x2f0008048c26a56e 0x17800402461352b7 0xc0000000000fe3ff 0xe00000000007f1ff

def z760 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xfbdc3ee3e7839f3f 0x7dee1f71f3c1cf9f

def z761 : W := mkw 0x5d0c2ca6cd87377a 0x2e86165366c39bbd 0x055c7bdfbf8cfcc6 0x82ae3defdfc67e63

def z762 : W := mkw 0xb41753a2c2e8d630 0x5a0ba9d161746b18 0x3423c3e3c07cff39 0x9a11e1f1e03e7f9c

def z763 : W := mkw 0xe01ff7fb7369c001 0xf00ffbfdb9b4e000 0xbffffffffbfde000 0xdffffffffdfef000

def z764 : W := mkw 0x091ff7ff7804214b 0x848ffbffbc0210a5 0xc11fb8c3800fe3ff 0xe08fdc61c007f1ff

def z765 : W := mkw 0x740c2ca2c5a39630 0x3a06165162d1cb18 0xfbfc3ce3c7f39f39 0xfdfe1e71e3f9cf9c

def z766 : W := mkw 0x0009b75370000001 0x8004dba9b8000000 0x3f83fffff8000000 0x1fc1fffffc000000

def z767 : W := mkw 0xab13d3552a7ce9cf 0x5589e9aa953e74e7 0x0423c31c387ce0c6 0x8211e18e1c3e7063

def z768 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xcfffff2047ffe318 0xe7ffff9023fff18c

def z769 : W := mkw 0x101ff7fb70801201 0x880ffbfdb8400900 0xffdfffffff831f39 0x7fefffffffc18f9c

def z770 : W := mkw 0x901ff7fb72c81201 0xc80ffbfdb9640900 0xfffffffffffc1f01 0xfffffffffffe0f80

def z771 : W := mkw 0x6d093f06cd27e57a 0x36849f836693f2bd 0xfe807f3ff80fe3ff 0xff403f9ffc07f1ff

def z772 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x15ff80d007f01c00 0x0affc06803f80e00

def z773 : W := mkw 0x9136c0f80ad83a8a 0x489b607c056c1d45 0x297f87c07ff3fc3e 0x14bfc3e03ff9fe1f

def z774 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0x8fffff0007fd6000 0x47ffff8003feb000

def z775 : W := mkw 0xc01a6c00074b0000 0x600d360003a58000 0xcfffff0007ffe000 0xe7ffff8003fff000

def z776 : W := mkw 0xd91e65a64bcd735a 0x6c8f32d325e6b9ad 0x825c452c5b8d6318 0x412e22962dc6b18c

def z777 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xba5c3ce3c3831f39 0x5d2e1e71e1c18f9c

def z778 : W := mkw 0x67093e03ed23a43f 0x33849f01f691d21f 0x28003f03f803e03e 0x14001f81fc01f01f

def z779 : W := mkw 0x101ff7fb70801211 0x880ffbfdb8400908 0x3f9ffffff8000318 0x1fcffffffc00018c

def z780 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x351ffbfff8000000 0x1a8ffdfffc000000

def z781 : W := mkw 0xe41b7f00876bc420 0x720dbf8043b5e210 0xcfffffc387fffc00 0xe7ffffe1c3fffe00

def z782 : W := mkw 0xe01b7f03776bc001 0xf00dbf81bbb5e000 0xcfffff0387ffe000 0xe7ffff81c3fff000

def z783 : W := mkw 0xcc3aec5ec75f0df0 0x661d762f63af86f8 0x2c23fc1fc07f00f8 0x9611fe0fe03f807c

def z784 : W := mkw 0x9032400002d81a80 0x48192000016c0d40 0xc7ffc00007fc1c00 0xe3ffe00003fe0e00

def z785 : W := mkw 0x540c24a2c1811630 0x2a06125160c08b18 0xbbdc3ce3c3811f39 0x5dee1e71e1c08f9c

def z786 : W := mkw 0x5413db59b5831631 0xaa09edacdac18b18 0xc443c31c3f831f39 0x6221e18e1fc18f9c

def z787 : W := mkw 0xc01a650003494000 0x600d328001a4a000 0xcfffc70007ffe000 0xe7ffe38003fff000

def z788 : W := mkw 0x000c24a240000000 0x0006125120000000 0x3b9c3cfff8000000 0x1dce1e7ffc000000

def z789 : W := mkw 0xbe375aada6ee9765 0x5f1bad56d3774bb2 0xaa5c7a2fa38e8326 0x552e3d17d1c74193

def z790 : W := mkw 0x000d37ab70000001 0x80069bd5b8000000 0x28003f2ff8000000 0x14001f97fc000000

def z791 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xffffc2fc27ffffff 0xffffe17e13ffffff

def z792 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x07ffc0c007f01c00 0x03ffe06003f80e00

def z793 : W := mkw 0x64093f02c523c430 0x32049f816291e218 0x08003f038003e000 0x04001f81c001f000

def z794 : W := mkw 0xe91b7f040f6fe14a 0x748dbf8207b7f0a5 0x317fb83c7ff003ff 0x18bfdc1e3ff801ff

def z795 : W := mkw 0x8012410002484000 0x4009208001242000 0xc7ffc10007fc6000 0xe3ffe08003fe3000

def z796 : W := mkw 0x9016c0f002d81a80 0x480b6078016c0d40 0xd7ffc0f007fc1fc1 0xebffe07803fe0fe0

def z797 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xd7ffc3fc3ffc1fc1 0xebffe1fe1ffe0fe0

def z798 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x7fa3faffa4729ce7 0xbfd1fd7fd2394e73

def z799 : W := mkw 0x981640a402cc1340 0x4c0b2052016609a0 0xd7ffc0fc07fc1fc1 0xebffe07e03fe0fe0

def z800 : W := mkw 0x001f77aa50000000 0x800fbbd528000000 0x3f9fffefd8000000 0x1fcffff7ec000000

def z801 : W := mkw 0x140c24a2c0801630 0x0a06125160400b18 0xfbdc3ce3c7801f39 0x7dee1e71e3c00f9c

def z802 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xfbdc3ce3c7839fff 0xfdee1e71e3c1cfff

def z803 : W := mkw 0xe01b7f01276bc001 0x700dbf8093b5e000 0xefffff03a7ffe000 0xf7ffff81d3fff000

def z804 : W := mkw 0x100480f000901a80 0x0802407800480d40 0x55ff80d007f01cc1 0xaaffc06803f80e60

def z805 : W := mkw 0x782dbffc05b7dbc0 0x3c16dffe02dbede0 0x18003ffc0003ffc1 0x0c001ffe0001ffe0

def z806 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x3d9fbafff8000000 0x1ecfdd7ffc000000

def z807 : W := mkw 0xe41b7f02c76bc430 0x720dbf8163b5e218 0xcfffff0387ffe000 0xe7ffff81c3fff000

def z808 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xd7ffc2fc27fc9fc7 0xebffe17e13fe4fe3

def z809 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0x017f80c007fc1cc0 0x80bfc06003fe0e60

def z810 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x011fb8efd8000000 0x008fdc77ec000000

def z811 : W := mkw 0x001b770370000001 0x800dbb81b8000000 0x3f9fff3ff8000000 0x1fcfff9ffc000000

def z812 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xc37ffd0007ffe000 0xe1bffe8003fff000

def z813 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0x017fb80007fce000 0x80bfdc0003fe7000

def z814 : W := mkw 0x001e65aa50000000 0x800f32d528000000 0x2a1c7d2fd8000000 0x150e3e97ec000000

def z815 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x7fbffffffc700000 0xbfdffffffe380000

def z816 : W := mkw 0x540408a085831630 0x2a02045042c18b18 0xfbdc38e387831f39 0x7dee1c71c3c18f9c

def z817 : W := mkw 0x100480f000901a80 0x0802407800480d40 0x017f80c007f01c00 0x00bfc06003f80e00

def z818 : W := mkw 0x9836c1fc12dc1bc0 0xcc1b60fe096e0de0 0xd7ffc1fc1ffc1fc1 0xebffe0fe0ffe0fe0

def z819 : W := mkw 0xe41b7f03f76bc431 0xf20dbf81fbb5e218 0xefffff03ffffe038 0xf7ffff81fffff01c

def z820 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0x157fc0fc07fc1fc1 0x8abfe07e03fe0fe0

def z821 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x79a3b8c384729ce7 0xbcd1dc61c2394e73

def z822 : W := mkw 0x192480ff78943bcb 0x8c92407fbc4a1de5 0x300000fff8001fff 0x1800007ffc000fff

def z823 : W := mkw 0x0000000000000000 0x0000000000000000 0x3f807ffff8000000 0x1fc03ffffc000000

def z824 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xffdc7fe3c7831f39 0x7fee3ff1e3c18f9c

def z825 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x3da3bad3a4709cc6 0x9ed1dd69d2384e63

def z826 : W := mkw 0xa01353000268c000 0x5009a98001346000 0x057fc30007fce000 0x82bfe18003fe7000

def z827 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x011fb8dfb8000000 0x008fdc6fdc000000

def z828 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xffffff3c7fffe0e7 0xffffff9e3ffff073

def z829 : W := mkw 0x993240040adc3bca 0x4c992002056e1de5 0xcfffc70007ffffff 0xe7ffe38003ffffff

def z830 : W := mkw 0x65093f02cd23e43a 0x32849f816691f21d 0x28003f03f803e03e 0x14001f81fc01f01f

def z831 : W := mkw 0x801ff7fb72480001 0xc00ffbfdb9240000 0x3ffffffffff00000 0x1ffffffffff80000

def z832 : W := mkw 0x720db6f361b19a95 0x3906db79b0d8cd4a 0x867f863063f183de 0xc33fc31831f8c1ef

def z833 : W := mkw 0x2600080084328ca4 0x1300040042194652 0x7ea0473c7c729ce7 0xbf50239e3e394e73

def z834 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xcbfffd0007ff6000 0x65fffe8003ffb000

def z835 : W := mkw 0x64093e02c5238430 0x32049f016291c218 0x28003e03c0038038 0x14001f01e001c01c

def z836 : W := mkw 0x66019a51a533cca5 0x3300cd28d299e652 0x7da3bad3a473fce7 0xbed1dd69d239fe73

def z837 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xdfffc2fc07fe9fc1 0xefffe17e03ff4fe0

def z838 : W := mkw 0x7f0008048db7bffe 0x3f80040246dbdfff 0xc060000007ffffff 0xe030000003ffffff

def z839 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x55a3bad3a4709cc7 0xaad1dd69d2384e63

def z840 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0xffa3fad3a47e9ce7 0xffd1fd69d23f4e73

def z841 : W := mkw 0xe0124800076bc000 0x7009240003b5e000 0xc17f800007ffe000 0xe0bfc00003fff000

def z842 : W := mkw 0x0001120120000001 0x0000890090000000 0x3e807f3ff8000000 0x1f403f9ffc000000

def z843 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xb35c3ce3c7811f39 0x59ae1e71e3c08f9c

def z844 : W := mkw 0x60093e0005238000 0x30049f000291c000 0xcfffff0007ffe000 0xe7ffff8003fff000

def z845 : W := mkw 0x903ff7fb72d81a81 0xc81ffbfdb96c0d40 0x7ffffffffff01cc1 0xbffffffffff80e60

def z846 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xd7ffc0fc5ffc1fd9 0xebffe07e2ffe0fec

def z847 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xc67fc03c07fc1fc1 0xe33fe01e03fe0fe0

def z848 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xffdc7fffff839fff 0xffee3fffffc1cfff

def z849 : W := mkw 0xe00488fb776bc001 0xf002447dbbb5e000 0xf06000ffffffe000 0xf830007ffffff000

def z850 : W := mkw 0x8812c054025c09c0 0x4409602a012e04e0 0xd7ffc0fc07fc1fc1 0xebffe07e03fe0fe0

def z851 : W := mkw 0xc01ff7fb73494001 0xe00ffbfdb9a4a000 0xffdffffffb8fe000 0xffeffffffdc7f000

def z852 : W := mkw 0xe01b7f02476bc010 0x700dbf8123b5e008 0xcfffff0047ffe018 0xe7ffff8023fff00c

def z853 : W := mkw 0x740c2ca2c5a3d630 0x3a06165162d1eb18 0xfbdc3ce3c783ff39 0x7dee1e71e3c1ff9c

def z854 : W := mkw 0x901640a002c81200 0x480b205001640900 0xc7ffc0c007fc1c00 0xe3ffe06003fe0e00

def z855 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x3f9ffffff8030038 0x1fcffffffc01801c

def z856 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x3523bad3a4709ce7 0x9a91dd69d2384e73

def z857 : W := mkw 0x66093e03e5238435 0x33049f01f291c21a 0x0000380380000000 0x00001c01c0000000

def z858 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xffdc3ef3e7831f39 0x7fee1f79f3c18f9c

def z859 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0xd7ffc0fc07fc1c00 0xebffe07e03fe0e00

def z860 : W := mkw 0x9832c05c02dc1bc0 0x4c19602e016e0de0 0xc7ffc01c07fc1fc1 0xe3ffe00e03fe0fe0

def z861 : W := mkw 0x000480fb70000001 0x8002407db8000000 0x398038fff8000000 0x1cc01c7ffc000000

def z862 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xc57ffb0007ffe000 0xe2bffd8003fff000

def z863 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xdfffc7fc07fc1fc1 0xefffe3fe03fe0fe0

def z864 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xd7ffc0fc07fe9fe7 0xebffe07e03ff4ff3

def z865 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x57ffc0fc07f01cc1 0xabffe07e03f80e60

def z866 : W := mkw 0x0013d35930000001 0x8009e9ac98000000 0x0503fbdfb8000000 0x0281fdefdc000000

def z867 : W := mkw 0x901640a002c81200 0x480b205001640900 0xffffc7e047ffff39 0xffffe3f023ffff9c

def z868 : W := mkw 0x26019a59b4328ca5 0x9300cd2cda194652 0x7da3badfbc729ce7 0xbed1dd6fde394e73

def z869 : W := mkw 0x9036c0fb72d81a81 0xc81b607db96c0d40 0x017f80c387f01c00 0x00bfc061c3f80e00

def z870 : W := mkw 0x192480fc08943bca 0x0c92407e044a1de5 0x100000fc38001fc7 0x0800007e1c000fe3

def z871 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xd7ffc3fc07fcffc1 0xebffe1fe03fe7fe0

def z872 : W := mkw 0x021ff7fb70100885 0x810ffbfdb8080442 0x3f9ffffff80000c6 0x1fcffffffc000063

def z873 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x6923bac3a4729ce7 0xb491dd61d2394e73

def z874 : W := mkw 0x9836c0fe42dc1bd0 0x4c1b607f216e0de8 0xd7ffc0fc47fc1fd9 0xebffe07e23fe0fec

def z875 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xffdc3ee3c7839f39 0xffee1f71e3c1cf9c

def z876 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xffffc2fc7ffe9fff 0xffffe17e3fff4fff

def z877 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x331ffdfff8000000 0x198ffefffc000000

def z878 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xd7ffc1fc1ffc7fc1 0xebffe0fe0ffe3fe0

def z879 : W := mkw 0x001f77a240000000 0x000fbbd120000000 0x3f9ffffff8000000 0x1fcffffffc000000

def z880 : W := mkw 0xe01b7f03776bc001 0xf00dbf81bbb5e000 0xffffff3fffffe000 0xffffff9ffffff000

def z881 : W := mkw 0x6f093e07ed27a57f 0x37849f03f693d2bf 0xfe807f3ff80fe3ff 0xff403f9ffc07f1ff

def z882 : W := mkw 0x801ff7fb72480001 0xc00ffbfdb9240000 0xbfdffffffb8c0000 0x5feffffffdc60000

def z883 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x179ffdffd8000000 0x0bcffeffec000000

def z884 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x057fc0c007fc1c00 0x82bfe06003fe0e00

def z885 : W := mkw 0x66093f03f5238435 0xb3049f81fa91c21a 0x28003f03f803803e 0x14001f81fc01c01f

def z886 : W := mkw 0x000c24a240000000 0x0006125120000000 0x3b9c7defd8000000 0x1dce3ef7ec000000

def z887 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0xd7ffc0d007fc1cc1 0xebffe06803fe0e60

def z888 : W := mkw 0x0017d2fb70000001 0x800be97db8000000 0x3f9ffafff8000000 0x1fcffd7ffc000000

def z889 : W := mkw 0x001bf75b70000001 0x800dfbadb8000000 0x2f9fff1ff8000000 0x17cfff8ffc000000

def z890 : W := mkw 0x9936c0ff7adc3bcb 0xcc9b607fbd6e1de5 0xffffc7ffffffffff 0xffffe3ffffffffff

def z891 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x071ffffff8000000 0x038ffffffc000000

def z892 : W := mkw 0x66093e03e5238435 0x33049f01f291c21a 0x28003a03a0028026 0x14001d01d0014013

def z893 : W := mkw 0x090192552804214b 0x0480c92a940210a5 0xfd83bad3a00fe3ff 0xfec1dd69d007f1ff

def z894 : W := mkw 0x0000805000100880 0x0000402800080440 0xd7ff80d007f01cc1 0xebffc06803f80e60

def z895 : W := mkw 0x000ca4fb70000001 0x8006527db8000000 0x3f9c7ffff8000000 0x1fce3ffffc000000

def z896 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x7fa3ffd3a4729ce7 0xbfd1ffe9d2394e73

def z897 : W := mkw 0x54082c0085831630 0x2a04160042c18b18 0xfbdc3cc387831f39 0x7dee1e61c3c18f9c

def z898 : W := mkw 0x2600885084328ca4 0x1300442842194652 0x7da3b8d384729ce7 0xbed1dc69c2394e73

def z899 : W := mkw 0xa01b77000268c000 0x500dbb8001346000 0xcfffff0007fce000 0xe7ffff8003fe7000

def z900 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xc35c3ce3c7831f39 0x61ae1e71e3c18f9c

def z901 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xf7ffc0fc7ffc1fc1 0xfbffe07e3ffe0fe0

def z902 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x13ff80e007f01c00 0x09ffc07003f80e00

def z903 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0xbf9ffffff8010318 0x5fcffffffc00818c

def z904 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0xffa3baf3a4729fe7 0xffd1dd79d2394ff3

def z905 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x3b9fbcfff8000000 0x1dcfde7ffc000000

def z906 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0x317f80fc7ff01fff 0x18bfc07e3ff80fff

def z907 : W := mkw 0x140408a2c4821630 0x0a02045162410b18 0xfbdc38e3c7821f39 0x7dee1c71e3c10f9c

def z908 : W := mkw 0x8012c05002580880 0x40096028012c0440 0xc7ffc0c007fc1c00 0xe3ffe06003fe0e00

def z909 : W := mkw 0x090000040804214a 0x04800002040210a5 0xc600473c780fe3ff 0xe300239e3c07f1ff

def z910 : W := mkw 0xe41b7f00876bc430 0x720dbf8043b5e218 0xcfffff0007ffe038 0xe7ffff8003fff01c

def z911 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xffffc3fc3ffeffe7 0xffffe1fe1fff7ff3

def z912 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xf7ffc3fc7ffcffff 0xfbffe1fe3ffe7fff

def z913 : W := mkw 0x001bf75930000001 0x800dfbac98000000 0x3f9fffdfb8000000 0x1fcfffefdc000000

def z914 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xab5c3ce3c7831f38 0x55ae1e71e3c18f9c

def z915 : W := mkw 0x2f019a55ac36adef 0x1780cd2ad61b56f7 0x8323fdefdc7d7f18 0x4191fef7ee3ebf8c

def z916 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0x817f80c007fc1f00 0x40bfc06003fe0f80

def z917 : W := mkw 0x903ff7fb72d81a81 0xc81ffbfdb96c0d40 0xfffffffffff01f01 0x7ffffffffff80f80

def z918 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0xffffbad3a7f29ce7 0xffffdd69d3f94e73

def z919 : W := mkw 0x9836c0fe52dc1bc0 0xcc1b607f296e0de0 0xd7ffc0fc5ffc1fc1 0xebffe07e2ffe0fe0

def z920 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x3d9ffbdfb8000000 0x1ecffdefdc000000

def z921 : W := mkw 0xe61b7f01a76bc425 0x730dbf80d3b5e212 0xcfffff0387ffe000 0xe7ffff81c3fff000

def z922 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0x017f80c007f01fc1 0x00bfc06003f80fe0

def z923 : W := mkw 0xa01353000268c000 0x5009a98001346000 0xcfffc70007ffe000 0xe7ffe38003fff000

def z924 : W := mkw 0x001f77ab70000001 0x800fbbd5b8000000 0x2f9fff2ff8000000 0x17cfff97fc000000

def z925 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xffffff3c7fffe339 0xffffff9e3ffff19c

def z926 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0x0d7fff0007ffe000 0x86bfff8003fff000

def z927 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x011ff9cf98000000 0x008ffce7cc000000

def z928 : W := mkw 0x101ff7fb70801201 0x880ffbfdb8400900 0xbfdffffffb800300 0x5feffffffdc00180

def z929 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xfbdc3fe3ff831f39 0x7dee1ff1ffc18f9c

def z930 : W := mkw 0x8912c0540a5c29ca 0x4489602a052e14e5 0xffffc7fc7fffffff 0xffffe3fe3fffffff

def z931 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0x395c3ce3c7831f39 0x1cae1e71e3c18f9c

def z932 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xefffff0027ffe026 0xf7ffff8013fff013

def z933 : W := mkw 0xc01a650003494000 0x600d328001a4a000 0x837fc50007fd6000 0x41bfe28003feb000

def z934 : W := mkw 0x0013d35930000001 0x8009e9ac98000000 0x3f83fffff8000000 0x1fc1fffffc000000

def z935 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0xffa3bed3a4739ce7 0xffd1df69d239ce73

def z936 : W := mkw 0x8012400002480000 0x4009200001240000 0xd7ffc0c007fc1c01 0xebffe06003fe0e00

def z937 : W := mkw 0x001ff7fb70100881 0x800ffbfdb8080440 0x3fbffffff87000c0 0x9fdffffffc380060

def z938 : W := mkw 0x090000040804214a 0x04800002040210a5 0xffdc473c7f8fe3ff 0xffee239e3fc7f1ff

def z939 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xffffc7fc7fffffc1 0xffffe3fe3fffffe0

def z940 : W := mkw 0x0400885084120ca0 0x0200442842090650 0x7da3bad3a4729ce7 0xbed1dd69d2394e73

def z941 : W := mkw 0xa0135b00066ac000 0x5009ad8003356000 0xcffffb0007fee000 0xe7fffd8003ff7000

def z942 : W := mkw 0x8832c05c025c09c0 0x4419602e012e04e0 0xd7ffc0dc07fc1cc1 0xebffe06e03fe0e60

def z943 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xffffff1027ffe000 0xffffff8813fff000

def z944 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x3923bad3a4729ce7 0x1c91dd69d2394e73

def z945 : W := mkw 0x0017d2f920000001 0x000be97c90000000 0x3f9ffffff8000000 0x1fcffffffc000000

def z946 : W := mkw 0x000db7fb70000001 0x8006dbfdb8000000 0x3e807ffff8000000 0x1f403ffffc000000

def z947 : W := mkw 0x0017d3fb70000001 0x800be9fdb8000000 0x3d83fbfff8000000 0x1ec1fdfffc000000

def z948 : W := mkw 0x983640a402dc1bc0 0x4c1b2052016e0de0 0xd7ffc0e007fc1fc1 0xebffe07003fe0fe0

def z949 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x75a3b8d3a4701ce7 0xbad1dc69d2380e73

def z950 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x837f80e007f01f00 0x41bfc07003f80f80

def z951 : W := mkw 0xe01b77000369c000 0x700dbb8001b4e000 0xceffc70003ffe000 0xe77fe38001fff000

def z952 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xc17f80c007ffffff 0xe0bfc06003ffffff

def z953 : W := mkw 0xe01b77000369c000 0x700dbb8001b4e000 0x047fc30003fce000 0x823fe18001fe7000

def z954 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x3f9ffffff80ce000 0x9fcffffffc067000

def z955 : W := mkw 0x5d0008048d87377a 0x2e80040246c39bbd 0xc040000007831fff 0x6020000003c18fff

def z956 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xcfffff1c3fffe000 0xe7ffff8e1ffff000

def z957 : W := mkw 0x8012400002480000 0x4009200001240000 0xc7ffc50007fd6000 0xe3ffe28003feb000

def z958 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xc7fffb0007fce000 0xe3fffd8003fe7000

def z959 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0xcfffc7c007fffc00 0xe7ffe3e003fffe00

def z960 : W := mkw 0x090000040804214a 0x04800002040210a5 0xff8047fc7c0fffff 0xffc023fe3e07ffff

def z961 : W := mkw 0x401ff7fb71010011 0xa00ffbfdb8808008 0x3f9ffffff8010018 0x1fcffffffc00800c

def z962 : W := mkw 0x26019b51a432cca5 0x1300cda8d2196652 0x7da3bbd3a472fce7 0xbed1dde9d2397e73

def z963 : W := mkw 0x090c24a64804214a 0x04861253240210a5 0xfb9c3ce3c00fe3ff 0xfdce1e71e007f1ff

def z964 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xffffc4fc47fc1fc1 0xffffe27e23fe0fe0

def z965 : W := mkw 0x9836c0ff72dc1bc1 0xcc1b607fb96e0de0 0xd7ffc0ff87fc1fc1 0xebffe07fc3fe0fe0

def z966 : W := mkw 0x0009370370000001 0x80049b81b8000000 0x2c007f1ff8000000 0x16003f8ffc000000

def z967 : W := mkw 0x101ff7fb70801201 0x880ffbfdb8400900 0x3fdfffffff801c00 0x1fefffffffc00e00

def z968 : W := mkw 0x000ca4fb70000001 0x8006527db8000000 0x38003cfff8000000 0x1c001e7ffc000000

def z969 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xcbffbc0007ffe000 0xe5ffde0003fff000

def z970 : W := mkw 0xe61b7f03f76bc425 0xf30dbf81fbb5e212 0xefffff03ffffe026 0xf7ffff81fffff013

def z971 : W := mkw 0x001bf75120000001 0x000dfba890000000 0x3f9ffffff8000000 0x1fcffffffc000000

def z972 : W := mkw 0x501ff7fb71811211 0xa80ffbfdb8c08908 0xffdffffffb830339 0x7feffffffdc1819c

def z973 : W := mkw 0x8012c05002580880 0x40096028012c0440 0xffffc7d027fffce7 0xffffe3e813fffe73

def z974 : W := mkw 0xe01b77000369c000 0x700dbb8001b4e000 0x8fffff0003fde000 0xc7ffff8001fef000

def z975 : W := mkw 0xc01ff7fb73494001 0xe00ffbfdb9a4a000 0x3fdffffffb800000 0x1feffffffdc00000

def z976 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x379ff8fff8000000 0x1bcffc7ffc000000

def z977 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x7da3bafffc729ce7 0xbed1dd7ffe394e73

def z978 : W := mkw 0x0009370370000001 0x80049b81b8000000 0x2a007f2ff8000000 0x15003f97fc000000

def z979 : W := mkw 0x801b770002480000 0x400dbb8001240000 0xcfffff0007ffe000 0xe7ffff8003fff000

def z980 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xffffff3067ffe3ff 0xffffff9833fff1ff

def z981 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0xff9ffffff80c0000 0xffcffffffc060000

def z982 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x7da3baf3e4729fff 0xbed1dd79f2394fff

def z983 : W := mkw 0x401ff7fb71010001 0xa00ffbfdb8808000 0xbfdffffffb810000 0x5feffffffdc08000

def z984 : W := mkw 0xa0135a00066a8000 0x5009ad0003354000 0xcfffff0007ffe000 0xe7ffff8003fff000

def z985 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xfbdc7de3c78f7f39 0x7dee3ef1e3c7bf9c

def z986 : W := mkw 0x090000040804214a 0x04800002040210a5 0xffa3c73c7c7fe3ff 0xffd1e39e3e3ff1ff

def z987 : W := mkw 0xe0093e00076bc000 0x70049f0003b5e000 0xcfffbe0007ffe000 0xe7ffdf0003fff000

def z988 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xd7ffc3fc3fffffff 0xebffe1fe1fffffff

def z989 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0x55ffc0dc07fc1cc1 0xaaffe06e03fe0e60

def z990 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xffdc7cffc7831f39 0x7fee3e7fe3c18f9c

def z991 : W := mkw 0x993e65ae5acc334a 0xcc9f32d72d6619a5 0x825c452c5b8d6318 0x412e22962dc6b18c

def z992 : W := mkw 0xe01b7f02576bc000 0xf00dbf812bb5e000 0xcfffff005fffe000 0xe7ffff802ffff000

def z993 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x3b9ffdefd8000000 0x1dcffef7ec000000

def z994 : W := mkw 0xe41b7f00876bc420 0x720dbf8043b5e210 0xffffffd3a7fffce7 0xffffffe9d3fffe73

def z995 : W := mkw 0x2f0008048c36adee 0x17800402461b56f7 0x40200000047efce7 0xa0100000023f7e73

def z996 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x7f9ffffffc001c01 0x3fcffffffe000e00

def z997 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x2b1fffeff8000000 0x158ffff7fc000000

def z998 : W := mkw 0x100480f000901a80 0x0802407800480d40 0xd3ff80e007f01f01 0x69ffc07003f80f80

def z999 : W := mkw 0x9936c0ff7adc3bcb 0xcc9b607fbd6e1de5 0xf7ffc0fffffc1fff 0xfbffe07ffffe0fff

def z1000 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x0f9fffefd8000000 0x07cffff7ec000000

def z1001 : W := mkw 0x103ff7fb70901a81 0x881ffbfdb8480d40 0x3f9ffffff8001c00 0x1fcffffffc000e00

def z1002 : W := mkw 0x64093f008523c420 0x32049f804291e210 0x28003f038003e020 0x14001f81c001f010

def z1003 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xcfffff1027ffe0c6 0xe7ffff8813fff063

def z1004 : W := mkw 0x101ff7fb70901a81 0x880ffbfdb8480d40 0xfffffffffff01fc1 0xfffffffffff80fe0

def z1005 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x3da3bad3a4701ce7 0x1ed1dd69d2380e73

def z1006 : W := mkw 0x66093f01a523c425 0x33049f80d291e212 0x0000380380000000 0x00001c01c0000000

def z1007 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xcdffba0007ffe000 0xe6ffdd0003fff000

def z1008 : W := mkw 0x001f77ab70000001 0x800fbbd5b8000000 0x3b9c7feff8000000 0x1dce3ff7fc000000

def z1009 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xd7ffc0fc07fc1fff 0xebffe07e03fe0fff

def z1010 : W := mkw 0x1f0480f7e8943fff 0x0f82407bf44a1fff 0x300000fff8001fff 0x1800007ffc000fff

def z1011 : W := mkw 0x0001925120100881 0x0000c92890080440 0x7da3bad3a4729ce7 0xbed1dd69d2394e73

def z1012 : W := mkw 0x8933d35d3a5c29cb 0xc499e9ae9d2e14e5 0x0423c31c387ce0c6 0x8211e18e1c3e7063

def z1013 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0x0fffff0007fce000 0x87ffff8003fe7000

def z1014 : W := mkw 0x090000040804214a 0x04800002040210a5 0xba00473c780fe3ff 0x5d00239e3c07f1ff

def z1015 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x0f9fffdfb8000000 0x07cfffefdc000000

def z1016 : W := mkw 0x64093f02c523c430 0x32049f816291e218 0x28003c03c0030038 0x14001e01e001801c

def z1017 : W := mkw 0x9012400002c81200 0x4809200001640900 0xc7ffc00007fc1f01 0xe3ffe00003fe0f80

def z1018 : W := mkw 0xc01ff7fb73494001 0xe00ffbfdb9a4a000 0xfffffffffffd6000 0xfffffffffffeb000

def z1019 : W := mkw 0xe61b7f01a76bc425 0x730dbf80d3b5e212 0xffffff13a7ffe0e7 0xffffff89d3fff073

def z1020 : W := mkw 0x6f093f05ad27e56f 0x37849f82d693f2b7 0xfe807f3ff80fe3ff 0xff403f9ffc07f1ff

def z1021 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xfbdc3ce3c78fff39 0xfdee1e71e3c7ff9c

def z1022 : W := mkw 0x903ff7fb72c81201 0xc81ffbfdb9640900 0x3fdffffffb800000 0x1feffffffdc00000

def z1023 : W := mkw 0x06008851a4120ca5 0x03004428d2090652 0x7da3b8d3a4721ce7 0xbed1dc69d2390e73

def z1024 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x7123b8d3a4729ce7 0xb891dc69d2394e73

def z1025 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xc57fc0dc07fc1fc1 0xe2bfe06e03fe0fe0

def z1026 : W := mkw 0x192480fc08943bca 0x0c92407e044a1de5 0x100000fc00001fff 0x0800007e00000fff

def z1027 : W := mkw 0x8012c05002580880 0x40096028012c0440 0x55ff80d007f01cc1 0xaaffc06803f80e60

def z1028 : W := mkw 0xe61b7f00876bc424 0x730dbf8043b5e212 0xcfffff0007ffe026 0xe7ffff8003fff013

def z1029 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xd7ffc4fc47fd1fd9 0xebffe27e23fe8fec

def z1030 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xdfffc4fc07ff1fc1 0xefffe27e03ff8fe0

def z1031 : W := mkw 0x001ee5fa50000000 0x800f72fd28000000 0x3f9ffdffd8000000 0x1fcffeffec000000

def z1032 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x3c03fffff8000000 0x1e01fffffc000000

def z1033 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0x017f80ec07f01f00 0x00bfc07603f80f80

def z1034 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xd5ff80d007fc1fc1 0xeaffc06803fe0fe0

def z1035 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xd7ffc0fc07ffffc1 0xebffe07e03ffffe0

def z1036 : W := mkw 0x66093f01a523c425 0x33049f80d291e212 0x08003f038003e000 0x04001f81c001f000

def z1037 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xd3ff80fc07f01fc1 0x69ffc07e03f80fe0

def z1038 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xdfffc7fc07ffffff 0xefffe3fe03ffffff

def z1039 : W := mkw 0x9836c1fc02dc5bc0 0x4c1b60fe016e2de0 0xd7ffc1fc07fc7fc1 0xebffe0fe03fe3fe0

def z1040 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x3fffc7fc7ff01c00 0x1fffe3fe3ff80e00

def z1041 : W := mkw 0xfd0008048feff77a 0x7e80040247f7fbbd 0xc060000007ffffff 0xe030000003ffffff

def z1042 : W := mkw 0x66093e01a5238425 0x33049f00d291c212 0x28003e03a0038026 0x14001f01d001c013

def z1043 : W := mkw 0xe01a6d00076bc000 0x700d368003b5e000 0xc7ffc50007ffe000 0xe3ffe28003fff000

def z1044 : W := mkw 0x000592fb70000001 0x8002c97db8000000 0x3103b8fff8000000 0x1881dc7ffc000000

def z1045 : W := mkw 0x001bf75b70000001 0x800dfbadb8000000 0x0403fb1fb8000000 0x0201fd8fdc000000

def z1046 : W := mkw 0x1d2480fec8943ffa 0x0e92407f644a1ffd 0x300000fff8001fff 0x1800007ffc000fff

def z1047 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0x17ffc0fc07fc1cc0 0x8bffe07e03fe0e60

def z1048 : W := mkw 0x001e65aa50000000 0x800f32d528000000 0x3f9c7ffff8000000 0x1fce3ffffc000000

def z1049 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xc7ffc0c007fc1fc1 0xe3ffe06003fe0fe0

def z1050 : W := mkw 0x9832400402dc1bc0 0x4c192002016e0de0 0xc17f800007fc1fc1 0xe0bfc00003fe0fe0

def z1051 : W := mkw 0x500c24a241811210 0x2806125120c08908 0xfbdc3ce3c7811f19 0x7dee1e71e3c08f8c

def z1052 : W := mkw 0xe01b7f02476bc000 0x700dbf8123b5e000 0xefffff03c7ffe000 0xf7ffff81e3fff000

def z1053 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xffffff0007ffe021 0xffffff8003fff010

def z1054 : W := mkw 0x001e65aa50000000 0x800f32d528000000 0x031c7defd8000000 0x018e3ef7ec000000

def z1055 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xdfffff3c07ffe000 0xefffff9e03fff000

def z1056 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xffdc7fffff8fff39 0xffee3fffffc7ff9c

def z1057 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0x8b7fff0007ffe000 0x45bfff8003fff000

def z1058 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0xffdfffffff800000 0x7fefffffffc00000

def z1059 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xffffc6fc67ff9fff 0xffffe37e33ffcfff

def z1060 : W := mkw 0x192480fc08943bca 0x0c92407e044a1de5 0x100000fc58001fd9 0x0800007e2c000fec

def z1061 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xd7ffc5fc07fd7fc1 0xebffe2fe03febfe0

def z1062 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0xd7ff80f007f01fc1 0xebffc07803f80fe0

def z1063 : W := mkw 0x001f77ab70000001 0x800fbbd5b8000000 0x3e9c7f3ff8000000 0x1f4e3f9ffc000000

def z1064 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xefffff007fffe000 0xf7ffff803ffff000

def z1065 : W := mkw 0x8012400002480000 0x4009200001240000 0xc7ffc00007ffe000 0xe3ffe00003fff000

def z1066 : W := mkw 0x501ff7fb71811211 0xa80ffbfdb8c08908 0x3fdffffffb800000 0x1feffffffdc00000

def z1067 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xffffc4fc7fff1fff 0xffffe27e3fff8fff

def z1068 : W := mkw 0x001f77ab70000001 0x800fbbd5b8000000 0x021c7d2fd8000000 0x010e3e97ec000000

def z1069 : W := mkw 0xd01ff7fb73c95211 0xe80ffbfdb9e4a908 0xbfdffffffb8d6318 0x5feffffffdc6b18c

def z1070 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xfbdc3cffff831f39 0x7dee1e7fffc18f9c

def z1071 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xffffc7fc7ffd7fd9 0xffffe3fe3ffebfec

def z1072 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xf7ffc0fc7fffffff 0xfbffe07e3fffffff

def z1073 : W := mkw 0x67093f01ad23e42f 0x33849f80d691f217 0x28003f03f803e03e 0x14001f81fc01f01f

def z1074 : W := mkw 0x001ee4fb70000001 0x800f727db8000000 0x3f9ffcfff8000000 0x1fcffe7ffc000000

def z1075 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x117f80e007f01f01 0x08bfc07003f80f80

def z1076 : W := mkw 0x9016c0f802c81200 0x480b607c01640900 0xd7ffc0fc07fc1f01 0xebffe07e03fe0f80

def z1077 : W := mkw 0x26019251a0308ca5 0x1300c928d0184652 0x3da3bad3a0709ce7 0x9ed1dd69d0384e73

def z1078 : W := mkw 0xe01b77000369c000 0x700dbb8001b4e000 0xc7ffc70007fde000 0xe3ffe38003fef000

def z1079 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x3f9ffffff8028026 0x1fcffffffc014013

def z1080 : W := mkw 0x0d0008048c06256a 0x06800402460312b5 0xc0000000040fffff 0xe00000000207ffff

def z1081 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xfffff8ff87fc1fc1 0xfffffc7fc3fe0fe0

def z1082 : W := mkw 0x9836c0fd22dc1bc1 0x4c1b607e916e0de0 0xf7ffc0ffa7fc1fc1 0xfbffe07fd3fe0fe0

def z1083 : W := mkw 0x0001925930000001 0x8000c92c98000000 0x3d83badfb8000000 0x1ec1dd6fdc000000

def z1084 : W := mkw 0x9a36c0fd22dc1bc5 0x4d1b607e916e0de2 0xd7ffc0fc27fc1fc7 0xebffe07e13fe0fe3

def z1085 : W := mkw 0x8012400002580880 0x40092000012c0440 0xc7ffc00007fc1cc1 0xe3ffe00003fe0e60

def z1086 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x0123b8c384709cc6 0x8091dc61c2384e63

def z1087 : W := mkw 0xa01ff7fb7268c001 0xd00ffbfdb9346000 0xffbffffff87fe000 0xffdffffffc3ff000

def z1088 : W := mkw 0xe01b77000369c000 0x700dbb8001b4e000 0x827fc50003fd6000 0x413fe28001feb000

def z1089 : W := mkw 0x0008240240000000 0x0004120120000000 0x3e807f3ff8000000 0x1f403f9ffc000000

def z1090 : W := mkw 0x26019b51b4328ca5 0x9300cda8da194652 0x7da3bbd3bc729ce7 0xbed1dde9de394e73

def z1091 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x7f9ffffff8028000 0xbfcffffffc014000

def z1092 : W := mkw 0x982480f402dc1bc0 0x4c12407a016e0de0 0xd7ff80f007fc1fc1 0xebffc07803fe0fe0

def z1093 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xffffc7fc27ffffe7 0xffffe3fe13fffff3

def z1094 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0xc3ff80c007f01c00 0x61ffc06003f80e00

def z1095 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xc7fffd0007fd6000 0xe3fffe8003feb000

def z1096 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0xfbff84e047f31f39 0x7dffc27023f98f9c

def z1097 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xf9dc38c387831f39 0x7cee1c61c3c18f9c

def z1098 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x4da3bac384729ce7 0xa6d1dd61c2394e73

def z1099 : W := mkw 0x2201925120308885 0x1100c92890184442 0x7da3bad3a4709cc7 0xbed1dd69d2384e63

def z1100 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xc7fff80007ffe000 0xe3fffc0003fff000

def z1101 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0x877fc0fc07fc1fc0 0xc3bfe07e03fe0fe0

def z1102 : W := mkw 0x001bf75b70000001 0x800dfbadb8000000 0x3e83ff3ff8000000 0x1f41ff9ffc000000

def z1103 : W := mkw 0x66093f03e523c435 0x33049f81f291e21a 0x28003f03e003e03e 0x14001f81f001f01f

def z1104 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xf7ffc5fc7ffd7fff 0xfbffe2fe3ffebfff

def z1105 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x3c23bad3a0729ce7 0x9e11dd69d0394e73

def z1106 : W := mkw 0x100c24a240801200 0x0806125120400900 0xfbdc3ce3c7831f39 0x7dee1e71e3c18f9c

def z1107 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0x4dfffb0007fee000 0xa6fffd8003ff7000

def z1108 : W := mkw 0x2f0008048c36adee 0x17800402461b56f7 0x4020000004729fff 0xa010000002394fff

def z1109 : W := mkw 0x000db6fb70000001 0x8006db7db8000000 0x3f9fbefff8000000 0x1fcfdf7ffc000000

def z1110 : W := mkw 0x801ff7fb72480001 0xc00ffbfdb9240000 0x3fbffffff87c0000 0x9fdffffffc3e0000

def z1111 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0xd7ffc0fc07f01f01 0x6bffe07e03f80f80

def z1112 : W := mkw 0x66093e03e5238435 0x33049f01f291c21a 0x28003c03c0030038 0x14001e01e001801c

def z1113 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x0123b8c384701ce7 0x0091dc61c2380e73

def z1114 : W := mkw 0x001ee4fa40000000 0x000f727d20000000 0x3f9ffffff8000000 0x1fcffffffc000000

def z1115 : W := mkw 0x1016c0f800901a80 0x080b607c00480d40 0xd7ffc0fc07f01fc1 0xebffe07e03f80fe0

def z1116 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0x937fc0fc07fc1fc1 0x49bfe07e03fe0fe0

def z1117 : W := mkw 0xab33d25d2a7ca9cf 0x5599e92e953e54e7 0x0423c31c387ce0c6 0x8211e18e1c3e7063

def z1118 : W := mkw 0xdd2008048fdf3ffa 0x6e90040247ef9ffd 0xc060000007ffffff 0xe030000003ffffff

def z1119 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0x017f80dc07f01cc0 0x00bfc06e03f80e60

def z1120 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xffdc7ce3c78f1f39 0xffee3e71e3c78f9c

def z1121 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xcbdc3cc387831f39 0x65ee1e61c3c18f9c

def z1122 : W := mkw 0xe0135b00076bc000 0x7009ad8003b5e000 0xc7ffc30007ffe000 0xe3ffe18003fff000

def z1123 : W := mkw 0x000d37a370000001 0x80069bd1b8000000 0x3f9c7ffff8000000 0x1fce3ffffc000000

def z1124 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xd17f80fc07fc1fc1 0xe8bfc07e03fe0fe0

def z1125 : W := mkw 0x540c2da2d5831630 0xaa0616d16ac18b18 0xfbdc3de3df831f39 0x7dee1ef1efc18f9c

def z1126 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x7da3fbd3a47efce7 0xbed1fde9d23f7e73

def z1127 : W := mkw 0x9836c0fe42dc1bc0 0x4c1b607f216e0de0 0xf7ffc0ffc7fc1fc1 0xfbffe07fe3fe0fe0

def z1128 : W := mkw 0xe61b7f01a76bc425 0x730dbf80d3b5e212 0xffffffc3a7fffc27 0xffffffe1d3fffe13

def z1129 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xffffc5fc5fff7ff9 0xffffe2fe2fffbffc

def z1130 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xc97fbf0007ffe000 0xe4bfdf8003fff000

def z1131 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xdfffff1007ffe0c1 0xefffff8803fff060

def z1132 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xd3dc38e387831f39 0x69ee1c71c3c18f9c

def z1133 : W := mkw 0x9832c05402dc1bc0 0x4c19602a016e0de0 0xd7ffc0d007fc1fc1 0xebffe06803fe0fe0

def z1134 : W := mkw 0x26011a0084328ca4 0x13008d0042194652 0x7da3bac384729ce7 0xbed1dd61c2394e73

def z1135 : W := mkw 0x001ff7fb70100881 0x800ffbfdb8080440 0x7fbffffffc729ce7 0xbfdffffffe394e73

def z1136 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0xff9ffffff80fe339 0xffcffffffc07f19c

def z1137 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xffffc4fc47ffffff 0xffffe27e23ffffff

def z1138 : W := mkw 0xe21b7f01276bc005 0x710dbf8093b5e002 0xcfffff0027ffe006 0xe7ffff8013fff003

def z1139 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xc37fc0ec07fc1fc1 0xe1bfe07603fe0fe0

def z1140 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xd7ffc5fc5ffc1fc1 0xebffe2fe2ffe0fe0

def z1141 : W := mkw 0xe0124800076bc000 0x7009240003b5e000 0xcfffc70007ffe000 0xe7ffe38003fff000

def z1142 : W := mkw 0x0001925120000001 0x0000c92890000000 0x3d83bafff8000000 0x1ec1dd7ffc000000

def z1143 : W := mkw 0xc01a650003494000 0x600d328001a4a000 0x867fc50003fd6000 0xc33fe28001feb000

def z1144 : W := mkw 0xc012400003494000 0x6009200001a4a000 0xc7ffc00007fd6000 0xe3ffe00003feb000

def z1145 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x3a1c7ffff8000000 0x1d0e3ffffc000000

def z1146 : W := mkw 0x66093f03f523c425 0xb3049f81fa91e212 0x28003f03f803e026 0x14001f81fc01f013

def z1147 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0xff9ffffff80fe0e7 0xffcffffffc07f073

def z1148 : W := mkw 0x201ff7fb70208001 0x900ffbfdb8104000 0x3fbffffff8708000 0x9fdffffffc384000

def z1149 : W := mkw 0x540c2caad5831630 0xaa0616556ac18b18 0xfbdc3cefdf831f39 0x7dee1e77efc18f9c

def z1150 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xf3dc38e3c7801f39 0x79ee1c71e3c00f9c

def z1151 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xdfffffc007fffc01 0xefffffe003fffe00

def z1152 : W := mkw 0x201ff7fb7020c001 0x900ffbfdb8106000 0x3f9ffffff800e000 0x1fcffffffc007000

def z1153 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0x817fb80007fd6000 0x40bfdc0003feb000

def z1154 : W := mkw 0x401ff7fb71014001 0xa00ffbfdb880a000 0x3f9ffffff8016000 0x1fcffffffc00b000

def z1155 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0x97ffc0fc07fc1f00 0x4bffe07e03fe0f80

def z1156 : W := mkw 0x8016c0f802580880 0x400b607c012c0440 0xd7ffc0fc07fc1cc1 0xebffe07e03fe0e60

def z1157 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0xffa3fffffc7ffce7 0xffd1fffffe3ffe73

def z1158 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x7da3bed3e4739cff 0xbed1df69f239ce7f

def z1159 : W := mkw 0x66093f008523c424 0x33049f804291e212 0x08003f000003e026 0x04001f800001f013

def z1160 : W := mkw 0x06019251a0100ca5 0x0300c928d0080652 0x7da3bad3a4701ce7 0xbed1dd69d2380e73

def z1161 : W := mkw 0xef0008048f7fedee 0x7780040247bff6f7 0xc060000007ffffff 0xe030000003ffffff

def z1162 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0xfda3bad3a47ffce7 0xfed1dd69d23ffe73

def z1163 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x7f9ffffff8020021 0x3fcffffffc010010

def z1164 : W := mkw 0x000db7fb70000001 0x8006dbfdb8000000 0x3d83bffff8000000 0x1ec1dffffc000000

def z1165 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x7f9ffffff80000c1 0xbfcffffffc000060

def z1166 : W := mkw 0xbf2008048efebfee 0x5f900402477f5ff7 0xc060000007ffffff 0xe030000003ffffff

def z1167 : W := mkw 0x5d0008048d87377a 0x2e80040246c39bbd 0xc0400000078f7f39 0x6020000003c7bf9c

def z1168 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0xffa3fff3e47fffff 0xffd1fff9f23fffff

def z1169 : W := mkw 0x2613db59b4328ca5 0x9309edacda194652 0x4423c31c3c729ce7 0xa211e18e1e394e73

def z1170 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0x815c38c387811f18 0x40ae1c61c3c08f8c

def z1171 : W := mkw 0x760c2ca2c5a39634 0x3b06165162d1cb1a 0xfbdc3ce3c7839f3f 0x7dee1e71e3c1cf9f

def z1172 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xdfffff2007ffe301 0xefffff9003fff180

def z1173 : W := mkw 0x24011a0084228420 0x12008d0042114210 0x7da3bad3a4729ce7 0xbed1dd69d2394e73

def z1174 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0x55ff80fc07f01fc1 0xaaffc07e03f80fe0

def z1175 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xd3dc3ce3c7811f19 0x69ee1e71e3c08f8c

def z1176 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x79a3b8d3a4721ce7 0x3cd1dc69d2390e73

def z1177 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xffffffc387ffe000 0xffffffe1c3fff000

def z1178 : W := mkw 0xe41b7f00876bc420 0x720dbf8043b5e210 0xffffffe3c7ffff39 0xfffffff1e3ffff9c

def z1179 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xffffc2fc27fc1fc1 0xffffe17e13fe0fe0

def z1180 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0xc17f80c007fc1c00 0xe0bfc06003fe0e00

def z1181 : W := mkw 0x66093f01a523c425 0x33049f80d291e212 0x28003a03a0028026 0x14001d01d0014013

def z1182 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x417f80c007f01cc1 0xa0bfc06003f80e60

def z1183 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x057fc0dc07f01c00 0x02bfe06e03f80e00

def z1184 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xc7ffc0ec07fc1f00 0xe3ffe07603fe0f80

def z1185 : W := mkw 0x0013d35930000001 0x8009e9ac98000000 0x2c03fb1fb8000000 0x1601fd8fdc000000

def z1186 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x7fa3bef3e4729ce7 0xbfd1df79f2394e73

def z1187 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xbbdc3ce3c7811f18 0x5dee1e71e3c08f8c

def z1188 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xd7ffc0fc07fd7fd9 0xebffe07e03febfec

def z1189 : W := mkw 0x801ff7fb72484001 0xc00ffbfdb9242000 0x3f9ffffff80c6000 0x1fcffffffc063000

def z1190 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xffffff2047ffe000 0xffffff9023fff000

def z1191 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0x015c38c387801f39 0x00ae1c61c3c00f9c

def z1192 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0x8e7fff0003ffe000 0xc73fff8001fff000

def z1193 : W := mkw 0xe0135a00076bc000 0x7009ad0003b5e000 0xcffffa0007ffe000 0xe7fffd0003fff000

def z1194 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0x837fc5ec5ffd7f18 0x41bfe2f62ffebf8c

def z1195 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xffffbce3c7f31f39 0xffffde71e3f98f9c

def z1196 : W := mkw 0xa01353000268c000 0x5009a98001346000 0x867fc30003fce000 0xc33fe18001fe7000

def z1197 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xffffc7fc7ffcffc7 0xffffe3fe3ffe7fe3

def z1198 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xffdc7ff3e78fffff 0xffee3ff9f3c7ffff

def z1199 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xfbdc7defdf831f39 0x7dee3ef7efc18f9c

def z1200 : W := mkw 0x541e6daad5831630 0xaa0f36d56ac18b18 0xc25c452c5f831f39 0x612e22962fc18f9c

def z1201 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xd3ffc0ec07fc1f01 0x69ffe07603fe0f80

def z1202 : W := mkw 0x801ff7fb72580881 0xc00ffbfdb92c0440 0xfffffffffffc1cc1 0xfffffffffffe0e60

def z1203 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xcfffff2c5fffe000 0xe7ffff962ffff000

def z1204 : W := mkw 0x901640a002c81200 0x480b205001640900 0xd3ff80e007f01f01 0x69ffc07003f80f80

def z1205 : W := mkw 0x5400080085831630 0x2a00040042c18b18 0xfec0473c7f831f39 0x7f60239e3fc18f9c

def z1206 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xffffc7fc7fff1ff9 0xffffe3fe3fff8ffc

def z1207 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0xff9ffffff8000301 0x7fcffffffc000180

def z1208 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0x3bdc3ce3c7801f39 0x1dee1e71e3c00f9c

def z1209 : W := mkw 0xe01b7f08176bc000 0xf00dbf840bb5e000 0xcfffff0c1fffe000 0xe7ffff860ffff000

def z1210 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xf7ffc0fc27fc1fe7 0xfbffe07e13fe0ff3

def z1211 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x2e1fff3ff8000000 0x170fff9ffc000000

def z1212 : W := mkw 0x190480f408943bca 0x0c82407a044a1de5 0xffffc7fc7fffffff 0xffffe3fe3fffffff

def z1213 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xfbdc3cf3e7831fff 0x7dee1e79f3c18fff

def z1214 : W := mkw 0x66093f01a523c425 0x33049f80d291e212 0xfe807f13a00fe0e7 0xff403f89d007f073

def z1215 : W := mkw 0x221ff7fb70208005 0x910ffbfdb8104002 0x3f9ffffff8008006 0x1fcffffffc004003

def z1216 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x7da3bfd3fc729ce7 0xbed1dfe9fe394e73

def z1217 : W := mkw 0xa01ff7fb7268c001 0xd00ffbfdb9346000 0x3fbffffff8700000 0x1fdffffffc380000

def z1218 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xcfffff0007ffe339 0xe7ffff8003fff19c

def z1219 : W := mkw 0x9032400002d81a80 0x48192000016c0d40 0x017f800007f01c00 0x00bfc00003f80e00

def z1220 : W := mkw 0x540c2da2c5835630 0x2a0616d162c1ab18 0xfbdc3de3c7837f39 0x7dee1ef1e3c1bf9c

def z1221 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x7da3bfd3a473fce7 0xbed1dfe9d239fe73

def z1222 : W := mkw 0x66093e03e5238435 0x33049f01f291c21a 0xfe803e33e00383ff 0xff401f19f001c1ff

def z1223 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x179ffbffb8000000 0x0bcffdffdc000000

def z1224 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x7dff82d027f29ce7 0xbeffc16813f94e73

def z1225 : W := mkw 0x221ff7fb70308885 0x910ffbfdb8184442 0x3fbffffff8700000 0x1fdffffffc380000

def z1226 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0xd7ffc0e007fc1f01 0xebffe07003fe0f80

def z1227 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x45ff80c007f01c00 0xa2ffc06003f80e00

def z1228 : W := mkw 0x983640ac02dc1bc0 0x4c1b2056016e0de0 0xc7ffc02c07fc1fc1 0xe3ffe01603fe0fe0

def z1229 : W := mkw 0x983640ac02cc1340 0x4c1b2056016609a0 0xd7ffc0ec07fc1f01 0xebffe07603fe0f80

def z1230 : W := mkw 0x993240040adc3bca 0x4c992002056e1de5 0xffffc73c7fffffff 0xffffe39e3fffffff

def z1231 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xffffc0fc07fe1fe1 0xffffe07e03ff0ff0

def z1232 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xefffff0047ffe038 0xf7ffff8023fff01c

def z1233 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xf7ffc0fc47fc1ff9 0xfbffe07e23fe0ffc

def z1234 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x3f9ffffff80080c6 0x9fcffffffc004063

def z1235 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0x79dc38e3c7821f39 0x3cee1c71e3c10f9c

def z1236 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xd7ffc0fc3ffc1fc7 0xebffe07e1ffe0fe3

def z1237 : W := mkw 0x221ff7fb70308885 0x910ffbfdb8184442 0x7fbffffff87280e7 0xbfdffffffc394073

def z1238 : W := mkw 0xd93e64ae4bcd335a 0x6c9f325725e699ad 0x825c452c5b8d6318 0x412e22962dc6b18c

def z1239 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xcbdc3ce3c7831f18 0x65ee1e71e3c18f8c

def z1240 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x51ff80c007f01c01 0x28ffc06003f80e00

def z1241 : W := mkw 0x66019a51a5338ca5 0x3300cd28d299c652 0xfde3bad3a7f39ce7 0xfef1dd69d3f9ce73

def z1242 : W := mkw 0x000592fb70000001 0x8002c97db8000000 0x3f83fffff8000000 0x1fc1fffffc000000

def z1243 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x7da3fbdfbc729ce7 0xbed1fdefde394e73

def z1244 : W := mkw 0x090000040804214a 0x04800002040210a5 0xff807ffff80fe3ff 0xffc03ffffc07f1ff

def z1245 : W := mkw 0xe41b7f00876bc420 0x720dbf8043b5e210 0xcfffff0007fffc21 0xe7ffff8003fffe10

def z1246 : W := mkw 0x001ee5fb70000001 0x800f72fdb8000000 0x3b9c7dfff8000000 0x1dce3efffc000000

def z1247 : W := mkw 0x001ff7fb70100881 0x800ffbfdb8080440 0x3f9ffffff8001cc1 0x1fcffffffc000e60

def z1248 : W := mkw 0x501ff7fb71811211 0xa80ffbfdb8c08908 0xffdfffffff811f19 0x7fefffffffc08f8c

def z1249 : W := mkw 0x66019a51a5338cb5 0x3300cd28d299c65a 0x7da3bad3a4739cff 0xbed1dd69d239ce7f

def z1250 : W := mkw 0x0001925120000001 0x0000c92890000000 0x3d83fbdfb8000000 0x1ec1fdefdc000000

def z1251 : W := mkw 0xe41b7f02c76bc430 0x720dbf8163b5e218 0xffffffc3c7fffc39 0xffffffe1e3fffe1c

def z1252 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x55a3b8d384729ce7 0xaad1dc69c2394e73

def z1253 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0x017ff90007fc6000 0x00bffc8003fe3000

def z1254 : W := mkw 0x100400a000801200 0x0802005000400900 0xd7ff80e007f01f01 0xebffc07003f80f80

def z1255 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xc7ffc0dc07fc1cc0 0xe3ffe06e03fe0e60

def z1256 : W := mkw 0x090000040804214a 0x04800002040210a5 0xae00473c780fe3fe 0xd700239e3c07f1ff

def z1257 : W := mkw 0x100480f000901a80 0x0802407800480d40 0xffff86f067f39fff 0xffffc37833f9cfff

def z1258 : W := mkw 0xe41b7f00876bc420 0x720dbf8043b5e210 0xefffff0387ffe020 0xf7ffff81c3fff010

def z1259 : W := mkw 0x9036c0fb72d81a81 0xc81b607db96c0d40 0x317f80fffff01c00 0x18bfc07ffff80e00

def z1260 : W := mkw 0x9836c0ff72dc1bc1 0xcc1b607fb96e0de0 0xffffc7fffffc1fc1 0xffffe3fffffe0fe0

def z1261 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0x017fc0cc07fc1c00 0x00bfe06603fe0e00

def z1262 : W := mkw 0xe01a6c00076bc000 0x700d360003b5e000 0xcffffc0007ffe000 0xe7fffe0003fff000

def z1263 : W := mkw 0x000db6f360000001 0x0006db79b0000000 0x3f9ffffff8000000 0x1fcffffffc000000

def z1264 : W := mkw 0x000ca4fb70000001 0x8006527db8000000 0x311c38fff8000000 0x188e1c7ffc000000

def z1265 : W := mkw 0x000db7fb70000001 0x8006dbfdb8000000 0x3b9c3ffff8000000 0x1dce1ffffc000000

def z1266 : W := mkw 0x9836c0fc02dc1bc0 0x4c1b607e016e0de0 0xffffc7fc47fffff9 0xffffe3fe23fffffc

def z1267 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xe95c3cc3c7831f39 0x74ae1e61e3c18f9c

def z1268 : W := mkw 0xe01b7f00076bc000 0x700dbf8003b5e000 0xcfffff0007ffe0e7 0xe7ffff8003fff073

def z1269 : W := mkw 0xa01240000268c000 0x5009200001346000 0xc7ffc00007fce000 0xe3ffe00003fe7000

def z1270 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x4da3bad3a4729cc6 0xa6d1dd69d2394e63

def z1271 : W := mkw 0x1f2480fda8943fef 0x0f92407ed44a1ff7 0x300000fff8001fff 0x1800007ffc000fff

def z1272 : W := mkw 0x901640a002c81200 0x480b205001640900 0x017f80c007f01c00 0x00bfc06003f80e00

def z1273 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xd7ffc7fc7ffdffdf 0xebffe3fe3ffeffef

def z1274 : W := mkw 0x9936c0fc0adc3bca 0x4c9b607e056e1de5 0xdfffc7fc3fffffc7 0xefffe3fe1fffffe3

def z1275 : W := mkw 0x0017d3f930000001 0x800be9fc98000000 0x3f9ffbffb8000000 0x1fcffdffdc000000

def z1276 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0xff9ffffff80383ff 0xffcffffffc01c1ff

def z1277 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0xffa3fffffc739fff 0xffd1fffffe39cfff

def z1278 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x117f80fc07f01c00 0x08bfc07e03f80e00

def z1279 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x391fbffff8000000 0x1c8fdffffc000000

def z1280 : W := mkw 0x001bf75b70000001 0x800dfbadb8000000 0x3d83ffdff8000000 0x1ec1ffeffc000000

def z1281 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0xc17f80c007f01f01 0x60bfc06003f80f80

def z1282 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0xfda3bad3a4739fff 0xfed1dd69d239cfff

def z1283 : W := mkw 0x000c24aa50000000 0x8006125528000000 0x3b9c3cefd8000000 0x1dce1e77ec000000

def z1284 : W := mkw 0x090000040804214a 0x04800002040210a5 0x3c00473c780fe3ff 0x9e00239e3c07f1ff

def z1285 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x0123b8d3a4701cc6 0x0091dc69d2380e63

def z1286 : W := mkw 0x540c2ca2c5831630 0x2a06165162c18b18 0xf15c38e3c7831f39 0x78ae1c71e3c18f9c

def z1287 : W := mkw 0x9836c0fd32dc1bc1 0xcc1b607e996e0de0 0xd7ffc0fc3ffc1fc1 0xebffe07e1ffe0fe0

def z1288 : W := mkw 0x101ff7fb70801201 0x880ffbfdb8400900 0x3f9ffffff8001f01 0x1fcffffffc000f80

def z1289 : W := mkw 0x221ff7fb70308885 0x910ffbfdb8184442 0x7fbffffffc709cc7 0xbfdffffffe384e63

def z1290 : W := mkw 0xe01b7f01376bc001 0xf00dbf809bb5e000 0xcfffff003fffe000 0xe7ffff801ffff000

def z1291 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x2d1fffdff8000000 0x168fffeffc000000

def z1292 : W := mkw 0x26019a51a4328ca5 0x1300cd28d2194652 0x2d23bad3a4729ce6 0x9691dd69d2394e73

def z1293 : W := mkw 0x9036c0f802d81a80 0x481b607c016c0d40 0x057f80d007f01cc0 0x82bfc06803f80e60

def z1294 : W := mkw 0x991640a40acc334a 0x4c8b2052056619a5 0xffffc7fc7fffffff 0xffffe3fe3fffffff

def z1295 : W := mkw 0x001ff7fb70000001 0x800ffbfdb8000000 0x3f9ffffff8000339 0x1fcffffffc00019c

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z4,z8,z6])],[(0,[z9,z7,z2,z3,z10,z5,z6]),(0,[z7,z2,z11,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z12,z13,z6]),(0,[z7,z14,z2,z3,z4,z15,z6]),(0,[z16,z2,z3,z4,z17,z5,z6]),(0,[z7,z2,z18,z4,z5,z6,z19]),(0,[z7,z2,z3,z5,z20,z6,z21]),(0,[z7,z2,z22,z3,z4,z5,z6])],[(0,[z23,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z24]),(0,[z7,z2,z25,z3,z4,z5,z6]),(0,[z7,z26,z2,z3,z4,z27,z6]),(0,[z7,z26,z2,z3,z28,z5,z6]),(0,[z7,z2,z3,z4,z29,z5,z6]),(0,[z7,z30,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z31,z5,z6]),(0,[z32,z2,z3,z4,z10,z5,z6]),(0,[z33,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z5,z6]),(1,[z7,z2,z3,z4,z5,z34]),(0,[z1,z7,z2,z3,z4,z17,z6]),(1,[z35,z2,z3,z4,z5,z6]),(0,[z7,z2,z36,z37,z3,z4,z6])],[(0,[z9,z2,z3,z4,z5,z13,z6]),(0,[z7,z2,z3,z4,z5,z38,z39]),(0,[z40,z41,z2,z3,z4,z5,z6])],[(0,[z7,z42,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z43,z5,z6]),(0,[z44,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z45,z3,z4,z5,z6]),(0,[z7,z2,z3,z46,z4,z27,z6]),(0,[z0,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z47,z48,z5,z6]),(0,[z7,z2,z37,z3,z4,z17,z6]),(0,[z7,z49,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z50,z4,z5,z6])],[(0,[z51,z7,z2,z3,z4,z5,z6]),(0,[z0,z52,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z53,z5,z6]),(0,[z54,z7,z2,z3,z4,z55,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z6,z56]),(0,[z7,z2,z3,z4,z57,z5,z6]),(0,[z7,z2,z3,z4,z58,z27,z6]),(0,[z7,z2,z3,z4,z59,z5,z6]),(0,[z7,z2,z3,z4,z12,z17,z6]),(0,[z7,z2,z3,z4,z60,z5,z6]),(0,[z7,z2,z36,z3,z4,z12,z6])],[(0,[z7,z2,z3,z61,z4,z5,z6]),(0,[z7,z2,z3,z62,z4,z5,z6])],[(0,[z9,z2,z63,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z64,z5,z6]),(1,[z52,z65,z3,z4,z5,z6]),(1,[z7,z2,z66,z3,z4,z6]),(0,[z7,z2,z3,z4,z67,z5,z6]),(0,[z7,z2,z3,z4,z12,z5,z20])],[(0,[z7,z2,z3,z68,z4,z5,z6]),(0,[z7,z2,z3,z69,z4,z5,z6]),(0,[z1,z7,z2,z3,z4,z27,z6]),(0,[z7,z70,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z27,z71,z6])],[(0,[z52,z7,z63,z3,z4,z5,z6]),(0,[z72,z7,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z73,z5,z13,z6]),(1,[z7,z2,z3,z4,z74,z6]),(0,[z75,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z17,z6,z21]),(0,[z7,z2,z3,z4,z5,z76,z6]),(0,[z7,z2,z77,z3,z4,z78,z5])],[(0,[z65,z2,z3,z69,z4,z5,z6]),(1,[z7,z2,z3,z4,z79,z6]),(0,[z7,z2,z3,z4,z27,z6,z80]),(0,[z7,z2,z3,z4,z81,z5,z6]),(0,[z7,z2,z82,z3,z4,z5,z6])],[(0,[z32,z0,z2,z3,z4,z5,z6]),(0,[z7,z2,z77,z3,z4,z5,z83]),(1,[z2,z3,z84,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z85]),(1,[z7,z2,z3,z4,z5,z86]),(1,[z2,z3,z4,z5,z87,z6]),(0,[z7,z2,z77,z3,z4,z78,z6])],[(0,[z7,z2,z3,z4,z88,z5,z6]),(0,[z7,z2,z3,z4,z89,z5,z6])]],
   [[(0,[z7,z2,z3,z90,z4,z5,z6]),(0,[z7,z2,z3,z91,z4,z5,z6]),(0,[z7,z2,z3,z4,z92,z5,z6]),(0,[z93,z7,z2,z3,z4,z5,z6]),(1,[z94,z2,z3,z4,z5,z6]),(0,[z7,z95,z2,z3,z4,z5,z6]),(0,[z7,z96,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z38]),(0,[z7,z2,z97,z4,z48,z5,z6])],[(0,[z7,z2,z3,z3,z4,z5,z6]),(0,[z98,z2,z3,z4,z5,z6,z83]),(0,[z7,z2,z3,z4,z99,z5,z6]),(0,[z7,z2,z36,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z100,z5,z6])],[(0,[z40,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z101,z4,z5,z6]),(0,[z7,z2,z102,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z103,z6]),(0,[z7,z2,z3,z4,z5,z104,z6]),(0,[z7,z2,z3,z105,z4,z78,z6])],[(0,[z106,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z107,z3,z4,z5,z6]),(0,[z7,z2,z3,z47,z4,z5,z6]),(0,[z108,z2,z3,z4,z109,z5,z6]),(0,[z7,z2,z110,z3,z4,z5,z6]),(1,[z7,z26,z2,z48,z5,z6]),(0,[z111,z95,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z112,z6])],[(0,[z40,z113,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z114,z5,z6]),(0,[z7,z115,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z116,z6]),(1,[z7,z2,z3,z4,z117,z6]),(0,[z7,z26,z2,z3,z48,z5,z6]),(0,[z2,z3,z28,z118,z4,z5,z6]),(0,[z119,z7,z2,z3,z4,z5,z6])],[(0,[z32,z7,z2,z120,z4,z5,z6]),(0,[z7,z2,z3,z121,z4,z5,z6]),(0,[z122,z7,z2,z3,z4,z27,z6])],[(0,[z32,z65,z2,z3,z4,z5,z6]),(0,[z7,z2,z123,z3,z4,z5,z6]),(0,[z124,z7,z2,z3,z4,z5,z6]),(0,[z125,z7,z2,z126,z4,z5,z6]),(1,[z7,z2,z127,z28,z5,z6])]],
   [[(0,[z65,z2,z3,z4,z5,z13,z6]),(0,[z128,z7,z2,z3,z4,z5,z6]),(0,[z7,z129,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z130,z6]),(0,[z7,z2,z131,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z132,z6,z19]),(1,[z7,z2,z77,z3,z4,z78])],[(0,[z7,z133,z2,z3,z4,z5,z6]),(0,[z134,z7,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z46,z4,z5,z6]),(0,[z135,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z136,z5,z6]),(1,[z7,z2,z3,z4,z132,z6])],[(0,[z7,z2,z3,z4,z137,z5,z6]),(0,[z0,z2,z3,z69,z4,z5,z6]),(0,[z138,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z139,z4,z5,z6]),(0,[z54,z7,z2,z140,z4,z5,z6]),(0,[z7,z2,z37,z3,z4,z5,z141]),(0,[z142,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z143,z5,z6])],[(0,[z7,z2,z3,z4,z144,z5,z6]),(1,[z7,z2,z3,z4,z145,z6]),(0,[z7,z2,z3,z4,z109,z17,z6]),(0,[z7,z2,z3,z146,z4,z27,z6]),(0,[z7,z2,z3,z4,z5,z58,z6]),(0,[z7,z2,z37,z4,z147,z5,z6]),(0,[z7,z2,z3,z4,z12,z5,z71]),(0,[z7,z2,z3,z148,z4,z5,z6]),(1,[z7,z2,z3,z4,z12,z149])],[(0,[z150,z7,z2,z151,z4,z5,z6]),(0,[z152,z7,z2,z3,z4,z73,z6]),(0,[z7,z2,z127,z97,z4,z5,z6]),(0,[z7,z2,z3,z4,z27,z6,z21])],[(0,[z9,z7,z2,z3,z69,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z153]),(0,[z113,z7,z2,z3,z4,z5,z6]),(0,[z111,z7,z2,z3,z4,z27,z6]),(0,[z7,z2,z3,z154,z4,z5,z6]),(0,[z7,z2,z155,z3,z4,z5,z6])],[(0,[z65,z2,z63,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z156,z5,z6]),(0,[z7,z2,z3,z4,z15,z5,z6]),(0,[z7,z157,z115,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z158,z6]),(0,[z7,z2,z159,z3,z4,z5,z6])],[(0,[z2,z3,z4,z10,z5,z13,z6]),(0,[z160,z7,z2,z3,z4,z5,z6]),(0,[z7,z161,z2,z3,z4,z74,z6]),(0,[z7,z2,z162,z3,z4,z5,z6]),(0,[z163,z7,z2,z3,z4,z5,z6]),(1,[z164,z2,z3,z4,z5,z6]),(0,[z7,z2,z165,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z166,z4,z5,z6]),(0,[z1,z23,z2,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z147,z27,z6]),(0,[z7,z2,z36,z3,z4,z167,z6])],[(0,[z150,z7,z2,z3,z4,z5,z168]),(0,[z7,z2,z46,z61,z4,z5,z6]),(0,[z7,z2,z3,z169,z4,z5,z6]),(0,[z7,z2,z170,z3,z4,z5,z6]),(0,[z35,z7,z2,z3,z4,z5,z6])],[(0,[z7,z157,z2,z3,z4,z17,z6]),(0,[z7,z2,z171,z3,z4,z5,z6])],[(0,[z98,z7,z2,z3,z4,z17,z6]),(0,[z7,z2,z172,z3,z4,z5,z6]),(0,[z7,z2,z3,z173,z4,z5,z6]),(0,[z7,z2,z3,z61,z4,z17,z6]),(0,[z174,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z109,z27,z6]),(1,[z16,z2,z3,z4,z17,z6]),(0,[z7,z175,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z176,z5,z6]),(0,[z7,z2,z3,z4,z5,z177,z6]),(0,[z7,z178,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z179,z4,z5,z6]),(0,[z7,z2,z3,z4,z17,z5,z6]),(0,[z7,z2,z37,z3,z4,z5,z180]),(0,[z7,z2,z3,z4,z5,z141,z6]),(0,[z7,z2,z3,z181,z4,z5,z6]),(0,[z7,z2,z3,z4,z182,z5,z6])],[(0,[z183,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z184,z6]),(0,[z98,z7,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z4,z5,z185,z6]),(0,[z7,z2,z3,z4,z5,z27,z6]),(0,[z186,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z187,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z188,z6]),(0,[z7,z2,z3,z189,z4,z5,z6]),(0,[z7,z2,z3,z4,z190,z5,z6])],[(0,[z7,z2,z3,z46,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z191,z6]),(0,[z7,z2,z3,z4,z192,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z193])]],
   [[(0,[z9,z7,z2,z3,z4,z5,z6]),(1,[z9,z2,z3,z69,z5,z6]),(0,[z0,z7,z2,z3,z4,z27,z6]),(1,[z7,z2,z3,z4,z194,z6]),(0,[z54,z7,z2,z3,z47,z5,z6]),(1,[z108,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z195,z6]),(0,[z7,z2,z3,z4,z5,z196,z6])],[(0,[z7,z2,z3,z197,z4,z5,z6]),(0,[z98,z9,z2,z3,z4,z5,z6]),(0,[z7,z2,z198,z3,z4,z5,z6]),(0,[z125,z7,z199,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z12,z5,z149])],[(0,[z7,z2,z3,z200,z4,z5,z6]),(0,[z2,z3,z4,z5,z13,z6,z83]),(0,[z7,z157,z2,z3,z4,z27,z6]),(0,[z7,z2,z201,z3,z4,z5,z6]),(0,[z7,z202,z2,z3,z4,z5,z6]),(0,[z7,z203,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z204])],[(0,[z205,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z61,z4,z27,z6]),(0,[z7,z2,z3,z4,z206,z27,z6]),(0,[z207,z7,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z208,z5,z6])],[(0,[z7,z2,z120,z97,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z209,z6]),(0,[z40,z7,z2,z3,z4,z17,z6]),(1,[z7,z2,z3,z4,z17,z6])],[(0,[z210,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z211,z27]),(0,[z7,z2,z3,z4,z5,z6,z21])],[(0,[z7,z2,z37,z3,z4,z5,z6])]],
   [[(0,[z52,z65,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z212,z5,z6]),(0,[z7,z2,z3,z4,z5,z213,z6]),(0,[z7,z2,z3,z4,z214,z5,z6])],[(0,[z7,z2,z3,z4,z215,z5,z6]),(1,[z23,z2,z120,z4,z5,z6]),(0,[z7,z2,z3,z4,z12,z5,z6])],[(0,[z7,z2,z3,z4,z5,z216,z6]),(0,[z7,z2,z3,z4,z5,z217,z6]),(0,[z7,z2,z3,z4,z5,z218,z6]),(0,[z7,z2,z131,z3,z4,z17,z6]),(0,[z7,z219,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z220,z6,z19]),(1,[z119,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z78,z6,z149])],[(1,[z7,z2,z3,z4,z5,z221]),(0,[z2,z3,z4,z190,z109,z5,z6]),(1,[z7,z2,z3,z4,z211,z5]),(0,[z222,z7,z2,z3,z4,z5,z6])],[(0,[z223,z2,z3,z4,z5,z6,z83]),(0,[z7,z2,z3,z4,z5,z6,z224]),(0,[z7,z2,z3,z225,z4,z5,z6])],[(0,[z40,z7,z2,z3,z4,z27,z6]),(0,[z226,z7,z2,z3,z4,z17,z6]),(0,[z7,z2,z3,z148,z4,z17,z6]),(1,[z2,z3,z118,z4,z5,z6]),(0,[z7,z2,z3,z4,z227,z5,z6]),(0,[z7,z2,z3,z4,z5,z228,z6])],[(0,[z7,z2,z3,z4,z229,z5,z6]),(0,[z7,z2,z3,z230,z4,z5,z6])],[(0,[z150,z7,z2,z3,z4,z231,z6]),(0,[z7,z2,z3,z232,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z233,z6]),(0,[z7,z2,z3,z4,z5,z234,z6]),(0,[z7,z115,z2,z3,z4,z27,z6]),(0,[z122,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z148,z4,z5,z20])]],
   [[(0,[z32,z2,z3,z4,z5,z6,z83]),(0,[z7,z2,z3,z4,z5,z6,z235]),(1,[z7,z2,z3,z4,z99,z6]),(1,[z236,z2,z3,z4,z5,z6]),(0,[z54,z7,z2,z3,z109,z5,z6]),(0,[z7,z2,z237,z3,z47,z5,z6]),(0,[z7,z2,z3,z4,z238,z17,z6]),(0,[z2,z3,z4,z17,z59,z5,z6]),(0,[z125,z94,z2,z3,z4,z5,z6])],[(0,[z239,z7,z2,z3,z4,z5,z6]),(0,[z98,z2,z3,z46,z4,z5,z6]),(0,[z7,z2,z3,z240,z4,z5,z6]),(0,[z7,z2,z241,z3,z4,z5,z6]),(0,[z7,z14,z2,z97,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z242,z6]),(1,[z2,z3,z4,z5,z243,z6])],[(0,[z2,z120,z3,z4,z10,z5,z6]),(0,[z7,z2,z36,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6,z244]),(0,[z7,z3,z4,z5,z39,z6,z80]),(0,[z7,z245,z2,z3,z4,z5,z6]),(0,[z7,z2,z77,z3,z4,z5,z21])],[(0,[z7,z2,z3,z246,z4,z5,z6]),(0,[z7,z247,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z148,z4,z27,z6])],[(0,[z7,z2,z3,z248,z4,z5,z6]),(0,[z249,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z17,z17,z6]),(0,[z7,z2,z3,z4,z5,z71,z80]),(0,[z7,z250,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z251])],[(0,[z7,z2,z3,z4,z5,z252,z6])]],
   [[(0,[z7,z2,z253,z3,z4,z5,z6]),(0,[z254,z7,z2,z3,z4,z5,z6]),(0,[z7,z161,z2,z3,z4,z17,z6]),(0,[z7,z2,z255,z3,z4,z5,z6])],[(0,[z256,z7,z2,z3,z4,z5,z6]),(0,[z98,z7,z2,z3,z69,z5,z6]),(0,[z7,z2,z3,z4,z257,z5,z6]),(1,[z7,z2,z3,z4,z5,z141]),(0,[z7,z258,z2,z3,z4,z5,z6]),(0,[z259,z7,z2,z3,z4,z5,z6])],[(0,[z7,z260,z2,z3,z4,z5,z6])],[(0,[z7,z261,z2,z3,z4,z5,z6]),(0,[z7,z2,z262,z3,z4,z17,z6]),(0,[z111,z7,z2,z3,z105,z4,z6]),(0,[z7,z2,z3,z4,z263,z5,z6])],[(0,[z7,z2,z151,z3,z4,z5,z6]),(0,[z264,z7,z2,z3,z4,z5,z6]),(0,[z265,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z109,z5,z6]),(0,[z2,z3,z4,z5,z20,z87,z6])],[(0,[z223,z7,z2,z3,z4,z17,z6]),(0,[z7,z2,z266,z3,z4,z5,z6]),(0,[z7,z2,z267,z3,z4,z5,z6])],[(0,[z7,z268,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z269]),(0,[z7,z2,z3,z4,z17,z27,z6]),(0,[z7,z2,z3,z4,z5,z270,z6])],[(0,[z7,z2,z3,z4,z5,z271,z6]),(0,[z7,z272,z2,z3,z4,z5,z6]),(1,[z41,z2,z3,z4,z5,z6]),(1,[z40,z7,z61,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z273,z6])]],
   [[(0,[z7,z274,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z275]),(0,[z7,z2,z237,z3,z109,z5,z6])],[(0,[z32,z7,z2,z3,z4,z17,z6]),(0,[z276,z7,z2,z3,z4,z5,z6]),(0,[z236,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z277,z4,z5,z6]),(0,[z7,z2,z3,z278,z4,z5,z6]),(0,[z7,z2,z3,z4,z279,z5,z6]),(0,[z7,z2,z280,z3,z4,z5,z6]),(0,[z44,z2,z36,z3,z4,z5,z6])],[(0,[z9,z7,z2,z3,z4,z27,z6]),(0,[z7,z2,z3,z4,z281,z5,z6]),(0,[z7,z2,z3,z4,z282,z5,z6]),(0,[z7,z2,z283,z3,z4,z5,z6])],[(0,[z7,z2,z3,z284,z4,z5,z6]),(0,[z0,z7,z2,z3,z4,z5,z83]),(0,[z7,z2,z3,z4,z5,z285,z6]),(0,[z7,z157,z2,z3,z4,z5,z6]),(1,[z7,z115,z3,z4,z27,z6]),(0,[z7,z2,z18,z3,z4,z17,z6]),(0,[z7,z2,z286,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z180])],[(0,[z7,z2,z3,z287,z4,z5,z6]),(0,[z98,z7,z2,z3,z4,z5,z6]),(0,[z288,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z145,z5,z6]),(0,[z7,z2,z289,z3,z4,z5,z6]),(0,[z54,z7,z3,z4,z109,z5,z6]),(0,[z7,z2,z3,z4,z206,z5,z6]),(1,[z16,z2,z3,z4,z5,z6]),(1,[z290,z2,z3,z4,z5,z6]),(0,[z7,z291,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z71,z243,z6]),(0,[z7,z2,z3,z292,z4,z5,z6])],[(0,[z7,z2,z3,z69,z47,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z293]),(0,[z223,z7,z2,z3,z4,z27,z6]),(0,[z40,z7,z2,z61,z4,z5,z6]),(0,[z7,z294,z2,z4,z5,z71,z6]),(0,[z7,z2,z3,z4,z5,z71,z21]),(0,[z7,z2,z3,z105,z4,z295,z6])],[(1,[z7,z2,z3,z296,z5,z6]),(0,[z7,z2,z3,z297,z4,z5,z6])],[(0,[z150,z7,z2,z3,z4,z5,z216]),(0,[z32,z9,z2,z3,z4,z5,z6]),(0,[z7,z2,z298,z3,z4,z5,z6]),(0,[z299,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z300])]],
   [[(0,[z7,z2,z301,z3,z4,z5,z6]),(0,[z7,z2,z302,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z8,z6]),(0,[z7,z2,z3,z4,z12,z5,z38]),(0,[z7,z2,z3,z47,z5,z6,z21]),(1,[z7,z2,z3,z303,z5,z6]),(1,[z7,z2,z3,z4,z5,z304])],[(0,[z7,z2,z3,z4,z305,z5,z6]),(0,[z7,z2,z3,z4,z5,z38,z6]),(0,[z2,z3,z84,z61,z4,z5,z6]),(0,[z7,z306,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z307,z6]),(0,[z7,z2,z37,z3,z4,z27,z6]),(0,[z7,z2,z127,z28,z4,z5,z6]),(0,[z7,z2,z4,z5,z71,z6,z19]),(0,[z7,z2,z308,z3,z4,z5,z6]),(0,[z7,z2,z36,z3,z5,z295,z6])],[(0,[z7,z2,z3,z4,z5,z6,z309]),(0,[z310,z7,z2,z3,z4,z5,z6]),(0,[z7,z311,z2,z3,z4,z5,z6]),(1,[z7,z2,z36,z3,z295,z6])],[(0,[z312,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z313,z6]),(0,[z7,z2,z18,z3,z4,z27,z6]),(0,[z7,z2,z3,z4,z12,z27,z6]),(0,[z314,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z315,z6])],[(1,[z7,z2,z90,z4,z5,z6]),(0,[z150,z98,z2,z3,z4,z5,z6]),(0,[z7,z2,z97,z46,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z316,z6]),(0,[z7,z3,z47,z4,z109,z5,z6]),(0,[z317,z7,z2,z3,z4,z17,z6]),(0,[z111,z318,z2,z3,z4,z5,z6]),(0,[z111,z7,z2,z37,z4,z5,z6])],[(0,[z319,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z221]),(0,[z7,z2,z3,z4,z5,z320,z6]),(0,[z7,z2,z321,z3,z4,z5,z6])],[(1,[z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z322,z4,z5,z6]),(0,[z7,z2,z3,z4,z78,z73,z6]),(0,[z7,z2,z3,z4,z27,z27,z6]),(0,[z7,z2,z3,z4,z5,z323,z6])],[(0,[z324,z7,z2,z3,z4,z5,z6]),(0,[z40,z7,z2,z3,z4,z5,z242]),(0,[z7,z2,z3,z4,z27,z188,z6])]],
   [[(1,[z113,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z130]),(0,[z7,z2,z18,z3,z4,z5,z19]),(0,[z7,z2,z3,z4,z12,z5,z19]),(0,[z325,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z105,z4,z12,z6])],[(0,[z7,z2,z97,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z5,z86,z6]),(0,[z7,z2,z3,z4,z5,z6,z326]),(0,[z7,z2,z3,z327,z4,z5,z6]),(0,[z7,z2,z3,z4,z328,z5,z6])],[(0,[z329,z7,z2,z3,z4,z5,z6]),(0,[z54,z7,z2,z3,z4,z79,z6]),(0,[z7,z2,z3,z4,z5,z330,z6])],[(0,[z7,z2,z3,z4,z331,z5,z6]),(0,[z152,z7,z2,z3,z4,z13,z6]),(0,[z7,z2,z3,z4,z5,z332,z6]),(0,[z7,z199,z3,z4,z5,z39,z6]),(0,[z7,z2,z3,z4,z5,z6,z333]),(0,[z334,z7,z2,z3,z4,z5,z6]),(0,[z335,z7,z2,z3,z4,z5,z6])],[(0,[z2,z3,z46,z69,z4,z5,z6]),(0,[z7,z115,z3,z4,z5,z27,z6]),(0,[z317,z7,z2,z3,z4,z27,z6]),(0,[z7,z2,z336,z3,z4,z5,z6]),(0,[z318,z7,z2,z3,z4,z5,z6])],[(0,[z150,z1,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z337,z6]),(0,[z7,z2,z3,z69,z109,z5,z6]),(0,[z7,z2,z338,z3,z4,z5,z6]),(0,[z40,z7,z2,z97,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z339]),(0,[z7,z2,z36,z3,z4,z27,z6]),(1,[z7,z2,z3,z4,z340,z6])],[(0,[z226,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z18,z3,z4,z5,z71])],[(0,[z52,z2,z3,z4,z10,z5,z6]),(0,[z7,z2,z341,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z10,z17,z6]),(0,[z342,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z4,z147,z5,z343,z6]),(0,[z7,z2,z3,z344,z4,z5,z6]),(0,[z7,z345,z2,z3,z4,z5,z6])]],
   [[(0,[z346,z7,z2,z3,z4,z5,z6]),(0,[z7,z347,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z348,z6])],[(1,[z150,z63,z3,z4,z5,z6]),(0,[z349,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z97,z3,z4,z27,z6]),(0,[z7,z2,z3,z4,z27,z213,z6]),(0,[z7,z2,z3,z4,z238,z5,z6])],[(0,[z7,z350,z2,z3,z4,z5,z6]),(0,[z351,z7,z2,z3,z4,z5,z6]),(0,[z152,z7,z2,z3,z4,z17,z6]),(0,[z7,z2,z3,z105,z4,z17,z6]),(0,[z7,z2,z352,z3,z4,z5,z6])],[(0,[z40,z7,z2,z3,z4,z313,z6]),(0,[z7,z2,z3,z353,z4,z5,z6])],[(0,[z7,z2,z28,z4,z48,z5,z6]),(0,[z7,z2,z354,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z355,z6]),(0,[z7,z2,z3,z356,z4,z5,z6]),(0,[z7,z2,z3,z4,z357,z5,z6]),(0,[z7,z2,z3,z4,z167,z17,z6]),(0,[z7,z2,z3,z4,z5,z6,z358])],[(1,[z7,z2,z3,z4,z103,z6])],[(0,[z2,z3,z46,z4,z5,z13,z6]),(0,[z152,z2,z3,z4,z5,z13,z6]),(0,[z7,z2,z359,z3,z4,z27,z6]),(1,[z2,z3,z4,z59,z5,z6]),(0,[z125,z7,z2,z77,z3,z4,z5])]],
   [[(0,[z360,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z361,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z4,z5,z38]),(1,[z7,z2,z179,z4,z5,z6]),(0,[z7,z2,z3,z28,z4,z17,z6]),(0,[z7,z2,z3,z126,z4,z5,z6]),(1,[z7,z2,z3,z4,z116,z6]),(0,[z7,z2,z3,z4,z5,z39,z6]),(1,[z111,z7,z2,z4,z343,z6]),(0,[z362,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z237,z3,z148,z5,z6])],[(1,[z7,z2,z3,z363,z5,z6]),(0,[z7,z161,z2,z3,z4,z5,z6]),(0,[z7,z2,z237,z3,z4,z5,z21])],[(0,[z152,z7,z2,z3,z4,z27,z6]),(1,[z70,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z275]),(0,[z7,z2,z3,z4,z17,z147,z6]),(0,[z7,z2,z364,z3,z4,z5,z6]),(0,[z7,z2,z3,z105,z167,z5,z6]),(0,[z7,z365,z2,z3,z4,z5,z6])],[(0,[z7,z2,z366,z3,z4,z5,z6]),(0,[z7,z97,z3,z61,z4,z5,z6]),(0,[z7,z2,z3,z4,z211,z5,z27]),(0,[z7,z2,z367,z3,z4,z5,z6]),(0,[z7,z2,z368,z3,z4,z5,z6])],[(0,[z2,z63,z3,z4,z10,z5,z6]),(0,[z40,z7,z2,z3,z4,z5,z369]),(0,[z7,z2,z262,z3,z4,z5,z6])],[(0,[z7,z2,z3,z370,z4,z5,z6]),(0,[z7,z2,z3,z4,z167,z27,z6]),(0,[z7,z2,z3,z371,z4,z5,z6]),(0,[z7,z2,z3,z4,z372,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z180])],[(0,[z373,z7,z2,z3,z4,z5,z6]),(0,[z98,z7,z2,z3,z4,z27,z6]),(0,[z223,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z374,z3,z4,z5,z6]),(0,[z125,z35,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z375,z6])],[(0,[z376,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z377,z6]),(0,[z7,z2,z3,z4,z74,z5,z6]),(0,[z7,z378,z2,z3,z4,z5,z6]),(0,[z7,z2,z379,z3,z4,z5,z6]),(1,[z95,z2,z3,z4,z5,z6]),(1,[z44,z2,z3,z4,z5,z6]),(0,[z7,z380,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z120,z3,z4,z5,z6,z83]),(0,[z7,z2,z3,z4,z5,z381,z6]),(0,[z7,z2,z3,z28,z4,z27,z6]),(1,[z7,z2,z3,z4,z382,z6]),(0,[z7,z2,z3,z105,z4,z167,z6]),(0,[z7,z2,z3,z4,z5,z6,z149])],[(0,[z7,z2,z3,z4,z5,z383,z6]),(0,[z7,z2,z3,z4,z5,z384,z6]),(0,[z385,z7,z2,z3,z4,z5,z6])],[(0,[z32,z7,z2,z3,z4,z5,z6]),(0,[z7,z386,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z17,z38,z6]),(0,[z7,z2,z3,z4,z211,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z304])],[(0,[z7,z65,z2,z3,z4,z17,z6]),(0,[z7,z2,z3,z387,z4,z5,z6]),(1,[z7,z2,z3,z388,z5,z6])],[(0,[z7,z389,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z390,z6]),(0,[z40,z7,z2,z3,z92,z5,z6]),(1,[z7,z2,z3,z189,z5,z6]),(0,[z40,z7,z2,z3,z189,z5,z6]),(0,[z125,z7,z2,z3,z4,z5,z39]),(0,[z7,z2,z18,z3,z4,z5,z6])],[(0,[z150,z7,z2,z3,z4,z184,z6]),(0,[z7,z2,z3,z4,z391,z5,z6]),(0,[z7,z2,z37,z3,z4,z147,z6])],[(0,[z7,z2,z3,z4,z5,z6,z392]),(0,[z7,z2,z3,z4,z12,z5,z83]),(0,[z393,z7,z2,z3,z4,z5,z6]),(0,[z394,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z395,z3,z4,z5,z6]),(0,[z7,z199,z2,z77,z3,z4,z5]),(0,[z7,z2,z396,z3,z4,z5,z6]),(0,[z7,z2,z37,z3,z105,z4,z6]),(0,[z7,z2,z3,z4,z397,z5,z6]),(0,[z7,z2,z398,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z73,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z6]),(1,[z7,z2,z3,z4,z27,z6]),(0,[z125,z7,z2,z3,z303,z5,z6]),(0,[z7,z2,z3,z4,z5,z399,z6])],[(0,[z7,z2,z3,z4,z400,z5,z6]),(0,[z7,z2,z401,z3,z4,z5,z6]),(0,[z2,z36,z280,z3,z4,z5,z6]),(0,[z7,z2,z402,z3,z4,z5,z6])],[(0,[z7,z2,z403,z3,z4,z5,z6]),(0,[z7,z2,z404,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z10,z5,z6]),(0,[z7,z2,z3,z405,z4,z5,z6]),(0,[z1,z7,z2,z3,z4,z73,z6]),(0,[z7,z406,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z17,z6,z407]),(0,[z7,z408,z2,z3,z4,z5,z6])],[(0,[z7,z65,z2,z3,z4,z27,z6]),(0,[z7,z2,z409,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z410,z6])],[(0,[z411,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z132,z5,z6]),(0,[z7,z412,z2,z3,z4,z5,z6])],[(0,[z317,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z413,z6]),(0,[z7,z414,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z17,z59,z6]),(0,[z7,z2,z3,z4,z375,z5,z6]),(0,[z415,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z416,z3,z4,z5,z6]),(0,[z7,z417,z2,z3,z4,z5,z6]),(0,[z418,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z148,z5,z21])],[(0,[z7,z2,z3,z419,z4,z5,z6])]],
   [[(0,[z420,z7,z2,z3,z4,z5,z6]),(0,[z125,z7,z2,z3,z4,z117,z6])],[(0,[z40,z7,z3,z61,z4,z5,z6]),(0,[z7,z2,z421,z3,z4,z5,z6])],[(0,[z150,z2,z3,z4,z5,z13,z6]),(0,[z7,z2,z3,z4,z27,z38,z6]),(0,[z7,z2,z97,z3,z4,z5,z6]),(0,[z7,z2,z3,z422,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z423,z6])],[(0,[z7,z424,z2,z3,z4,z5,z6]),(0,[z98,z23,z2,z3,z4,z5,z6]),(0,[z40,z7,z14,z3,z4,z5,z6]),(0,[z7,z2,z3,z425,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z426]),(0,[z7,z2,z3,z4,z427,z5,z6]),(0,[z7,z2,z428,z3,z4,z5,z6]),(0,[z111,z7,z2,z3,z4,z78,z6]),(1,[z7,z2,z3,z4,z5,z429]),(1,[z7,z2,z3,z105,z167,z6])],[(0,[z7,z2,z3,z4,z430,z5,z6]),(0,[z7,z199,z2,z3,z4,z5,z39]),(0,[z431,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z432,z6,z21]),(0,[z7,z433,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6,z434]),(0,[z7,z2,z3,z4,z435,z5,z6]),(1,[z2,z3,z4,z190,z5,z6]),(0,[z7,z294,z2,z3,z4,z5,z6]),(0,[z436,z2,z3,z4,z5,z71,z6]),(0,[z7,z2,z437,z3,z4,z5,z6]),(0,[z164,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z438,z4,z5,z6]),(0,[z7,z2,z3,z4,z73,z5,z6]),(0,[z7,z2,z3,z4,z439,z5,z6]),(0,[z290,z2,z3,z28,z4,z5,z6])],[(0,[z32,z7,z2,z46,z4,z5,z6]),(0,[z7,z440,z2,z3,z4,z5,z6])]],
   [[(0,[z150,z2,z63,z3,z4,z5,z6]),(0,[z7,z441,z2,z3,z4,z5,z6]),(0,[z442,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z10,z5,z6]),(0,[z7,z2,z359,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z17,z39,z6]),(0,[z7,z2,z3,z4,z382,z48,z6]),(0,[z7,z2,z3,z4,z5,z443,z6])],[(0,[z7,z2,z3,z4,z444,z5,z6]),(1,[z223,z2,z3,z4,z5,z83]),(0,[z360,z7,z2,z3,z4,z27,z6]),(0,[z7,z2,z3,z4,z5,z20,z39])],[(0,[z152,z7,z2,z3,z4,z5,z6]),(0,[z7,z161,z2,z3,z4,z27,z6]),(0,[z7,z2,z3,z105,z4,z5,z6])],[(0,[z7,z2,z3,z4,z13,z27,z6]),(0,[z7,z2,z445,z3,z4,z5,z6]),(0,[z125,z7,z2,z3,z4,z12,z5]),(0,[z7,z2,z3,z105,z4,z5,z399])],[(0,[z223,z7,z2,z3,z4,z5,z38]),(0,[z7,z2,z3,z388,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z71,z39])],[(0,[z1,z65,z2,z3,z4,z5,z6]),(0,[z7,z446,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z167,z5,z6]),(0,[z7,z2,z3,z148,z4,z5,z21])],[(0,[z7,z2,z3,z4,z5,z447,z6]),(0,[z448,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z449]),(1,[z125,z7,z3,z4,z5,z80]),(0,[z7,z2,z3,z4,z5,z39,z19])]],
   [[(0,[z125,z7,z2,z3,z4,z116,z6]),(0,[z7,z2,z3,z4,z5,z450,z6])],[(0,[z150,z2,z120,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z451,z6]),(0,[z7,z157,z3,z4,z17,z5,z6]),(0,[z7,z2,z3,z4,z17,z6,z149]),(0,[z7,z2,z3,z28,z4,z5,z6])],[(1,[z7,z157,z3,z4,z17,z6])],[(0,[z7,z14,z97,z3,z4,z5,z6])],[(0,[z52,z2,z3,z4,z5,z6,z83]),(0,[z32,z7,z2,z3,z4,z27,z6]),(0,[z7,z2,z3,z4,z211,z27,z6]),(1,[z7,z2,z452,z3,z4,z27]),(0,[z7,z2,z3,z4,z5,z20,z6]),(0,[z7,z2,z3,z4,z453,z5,z6])],[(0,[z7,z2,z3,z4,z78,z13,z6]),(0,[z7,z2,z454,z3,z4,z5,z6]),(0,[z7,z455,z2,z3,z4,z5,z6])],[(0,[z1,z7,z2,z3,z4,z5,z34]),(0,[z7,z2,z3,z4,z456,z5,z6]),(0,[z457,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z220,z5,z6]),(0,[z7,z2,z77,z3,z4,z12,z6])],[(0,[z2,z120,z3,z46,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z458,z6]),(0,[z7,z2,z459,z3,z4,z5,z6])]],
   [[(0,[z460,z7,z2,z3,z4,z5,z6]),(0,[z461,z7,z2,z3,z4,z5,z6]),(0,[z7,z462,z2,z3,z4,z5,z6]),(0,[z125,z7,z2,z3,z4,z17,z6]),(0,[z7,z26,z2,z3,z4,z5,z86]),(0,[z7,z2,z3,z4,z463,z5,z6]),(0,[z7,z2,z464,z3,z4,z5,z6])],[(0,[z465,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z466,z6]),(0,[z467,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z27,z39,z6]),(1,[z7,z2,z452,z3,z4,z5]),(1,[z2,z3,z4,z17,z59,z6]),(0,[z7,z2,z3,z4,z5,z468,z6]),(0,[z7,z2,z469,z3,z4,z5,z6])],[(0,[z7,z470,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z242]),(0,[z7,z2,z3,z471,z4,z5,z6]),(0,[z7,z472,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z473,z6]),(1,[z7,z2,z3,z4,z5,z399]),(0,[z7,z2,z3,z148,z5,z6,z21])],[(0,[z7,z2,z3,z4,z474,z5,z6])],[(0,[z150,z7,z65,z3,z4,z5,z6]),(0,[z7,z65,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z475,z6]),(0,[z7,z2,z3,z4,z17,z410,z6]),(0,[z7,z2,z3,z4,z5,z6,z407]),(0,[z7,z199,z2,z3,z4,z12,z5]),(0,[z7,z476,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z432,z5,z6])],[(0,[z7,z477,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z478,z4,z5,z6]),(0,[z479,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z480]),(1,[z7,z2,z3,z4,z432,z6])],[(0,[z150,z7,z2,z3,z296,z5,z6]),(0,[z481,z7,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z73,z6]),(0,[z482,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z12,z6,z149])],[(0,[z7,z483,z2,z3,z4,z5,z6]),(0,[z7,z161,z3,z47,z4,z5,z6]),(0,[z7,z294,z2,z3,z4,z17,z6]),(1,[z7,z2,z364,z4,z5,z6]),(0,[z7,z2,z3,z4,z484,z5,z6]),(1,[z2,z255,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z19]),(0,[z7,z2,z485,z3,z4,z5,z6])]],
   [[(0,[z486,z7,z2,z3,z4,z5,z6]),(0,[z125,z7,z2,z3,z4,z27,z6]),(0,[z7,z2,z77,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z487,z5,z6])],[(0,[z2,z63,z3,z4,z5,z6,z83]),(0,[z7,z2,z3,z4,z488,z5,z6]),(0,[z7,z489,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z27,z6,z149]),(0,[z2,z127,z255,z3,z4,z5,z6]),(0,[z490,z2,z127,z3,z4,z5,z6]),(0,[z7,z491,z2,z3,z4,z5,z6])],[(0,[z32,z2,z3,z46,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z34,z6]),(0,[z436,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z492,z3,z4,z5,z6]),(0,[z7,z2,z77,z3,z4,z5,z20])],[(0,[z0,z2,z3,z4,z5,z38,z6])],[(0,[z150,z7,z2,z90,z4,z5,z6]),(0,[z7,z2,z493,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z494]),(0,[z7,z2,z3,z4,z5,z6,z495]),(0,[z7,z3,z4,z17,z5,z27,z6]),(0,[z496,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z12,z5,z21])],[(0,[z52,z7,z2,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z497,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z498]),(0,[z7,z499,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z500,z5,z6])],[(0,[z150,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z501,z5,z6]),(0,[z23,z7,z2,z120,z4,z5,z6]),(1,[z7,z2,z3,z4,z313,z6]),(0,[z7,z2,z3,z4,z430,z27,z6]),(1,[z490,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z502,z6]),(0,[z7,z2,z3,z503,z4,z5,z6])],[(0,[z150,z52,z2,z3,z4,z5,z6]),(0,[z7,z294,z2,z3,z4,z27,z6]),(0,[z7,z2,z504,z3,z4,z5,z6])]],
   [[(0,[z505,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z73,z27,z6]),(0,[z506,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z77,z3,z4,z27,z6]),(0,[z7,z199,z2,z3,z4,z17,z6]),(0,[z111,z7,z2,z4,z5,z343,z6]),(1,[z436,z2,z3,z4,z5,z6]),(1,[z2,z280,z3,z4,z5,z6])],[(1,[z7,z2,z3,z4,z466,z6]),(0,[z32,z23,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z507,z6]),(0,[z7,z2,z127,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z303,z5,z6]),(0,[z7,z508,z2,z3,z4,z5,z6]),(0,[z7,z2,z66,z3,z4,z48,z6])],[(0,[z23,z2,z120,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z10,z27,z6]),(0,[z7,z2,z3,z509,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z510]),(0,[z7,z2,z3,z4,z117,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z511]),(0,[z7,z2,z3,z4,z5,z512,z6])],[(0,[z7,z513,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z514,z5,z6]),(0,[z7,z515,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z15,z6]),(0,[z16,z7,z2,z3,z4,z17,z6]),(0,[z7,z2,z66,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z516,z6])],[(0,[z7,z2,z3,z4,z5,z6,z517]),(1,[z7,z2,z126,z4,z5,z6]),(0,[z7,z294,z2,z3,z4,z5,z19])],[(0,[z518,z7,z2,z3,z4,z5,z6]),(0,[z52,z7,z2,z3,z4,z27,z6]),(0,[z519,z7,z2,z3,z4,z5,z6]),(0,[z520,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z39,z83]),(0,[z7,z2,z3,z105,z4,z27,z6]),(0,[z7,z2,z77,z3,z4,z5,z19])],[(0,[z98,z65,z2,z3,z4,z5,z6]),(0,[z521,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z522]),(0,[z7,z523,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z524,z4,z17,z6]),(0,[z7,z525,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z83]),(1,[z7,z2,z3,z4,z5,z369]),(0,[z7,z2,z3,z84,z4,z5,z6]),(0,[z7,z2,z3,z4,z526,z17,z6]),(0,[z7,z2,z3,z4,z5,z87,z6])]],
   [[(0,[z7,z2,z527,z3,z4,z5,z6]),(0,[z7,z2,z528,z3,z4,z5,z6]),(0,[z7,z199,z2,z3,z4,z27,z6])],[(0,[z7,z2,z3,z4,z5,z529,z6]),(0,[z7,z2,z127,z3,z4,z27,z6]),(0,[z7,z94,z2,z3,z4,z5,z6]),(0,[z7,z2,z127,z3,z28,z5,z6])],[(0,[z7,z26,z2,z4,z48,z5,z6]),(1,[z7,z2,z37,z4,z147,z6]),(0,[z7,z294,z2,z3,z4,z5,z71]),(0,[z119,z2,z3,z4,z5,z20,z6])],[(0,[z530,z7,z2,z3,z4,z5,z6]),(0,[z531,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z532,z5,z6]),(0,[z223,z7,z2,z3,z4,z5,z83]),(0,[z7,z2,z3,z109,z48,z5,z6]),(0,[z7,z2,z3,z533,z4,z5,z6]),(0,[z7,z2,z77,z3,z4,z5,z71])],[(0,[z0,z98,z2,z3,z4,z5,z6]),(0,[z7,z2,z534,z3,z4,z5,z6]),(0,[z7,z2,z535,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z19,z80]),(1,[z7,z199,z3,z4,z5,z39])],[(0,[z7,z2,z3,z4,z17,z73,z6]),(0,[z7,z2,z3,z4,z5,z38,z80]),(0,[z7,z2,z3,z4,z5,z6,z536]),(0,[z7,z2,z2,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z17,z20,z6]),(0,[z7,z2,z3,z4,z537,z5,z6]),(0,[z7,z538,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z539,z6]),(0,[z7,z2,z3,z540,z4,z5,z6])],[],[(0,[z7,z2,z541,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z542,z6]),(1,[z7,z2,z3,z92,z5,z6]),(0,[z7,z26,z2,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z543,z5,z6]),(0,[z544,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z545,z4,z5,z6]),(0,[z111,z7,z2,z3,z4,z343,z6]),(0,[z7,z2,z37,z3,z4,z78,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z546,z6]),(0,[z2,z3,z69,z4,z10,z5,z6]),(0,[z7,z2,z3,z547,z4,z5,z6]),(0,[z7,z2,z3,z4,z548,z5,z6]),(0,[z7,z2,z3,z105,z4,z5,z429])],[(0,[z150,z7,z2,z3,z363,z5,z6]),(0,[z7,z2,z120,z3,z4,z17,z6]),(0,[z1,z7,z2,z3,z4,z13,z6]),(0,[z549,z7,z2,z3,z4,z5,z6])],[(0,[z150,z2,z3,z69,z4,z5,z6]),(0,[z7,z550,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z551,z5,z6]),(0,[z7,z2,z3,z4,z5,z79,z6]),(1,[z7,z2,z3,z4,z55,z6]),(0,[z486,z7,z2,z3,z4,z17,z6]),(0,[z2,z3,z4,z12,z208,z5,z6])],[(0,[z52,z2,z3,z46,z4,z5,z6]),(0,[z7,z2,z3,z4,z48,z17,z6]),(0,[z7,z2,z3,z4,z5,z20,z19]),(0,[z552,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z553,z3,z4,z5,z6])],[(0,[z1,z152,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z83]),(0,[z554,z7,z2,z3,z4,z5,z6]),(0,[z54,z7,z2,z3,z4,z17,z6]),(0,[z7,z2,z2,z3,z4,z27,z6]),(0,[z7,z2,z3,z4,z5,z6,z555]),(0,[z7,z2,z3,z4,z5,z556,z6])],[(0,[z7,z2,z3,z4,z557,z5,z6]),(1,[z7,z3,z4,z17,z27,z6]),(0,[z7,z2,z452,z3,z4,z27,z6]),(0,[z7,z2,z3,z4,z5,z558,z6]),(0,[z7,z2,z3,z559,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z560])],[(1,[z32,z2,z46,z4,z5,z6]),(0,[z7,z294,z2,z61,z4,z5,z6]),(0,[z125,z7,z3,z4,z5,z6,z80]),(0,[z7,z2,z3,z4,z5,z343,z6]),(0,[z7,z561,z2,z3,z4,z5,z6]),(0,[z164,z2,z3,z4,z12,z5,z6])]],
   [[(0,[z150,z7,z2,z3,z4,z17,z6]),(0,[z23,z52,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z17,z6,z19]),(1,[z7,z2,z3,z4,z220,z6])],[(0,[z7,z2,z120,z3,z4,z27,z6]),(0,[z562,z7,z2,z3,z4,z5,z6]),(0,[z7,z14,z2,z3,z4,z194,z6]),(1,[z7,z2,z3,z4,z529,z6]),(0,[z125,z7,z2,z3,z4,z5,z6]),(0,[z563,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z20,z71]),(0,[z7,z2,z77,z3,z4,z5,z149])],[(0,[z7,z2,z3,z4,z363,z5,z6]),(0,[z7,z2,z3,z4,z12,z73,z6]),(0,[z7,z2,z3,z4,z564,z5,z6]),(0,[z7,z2,z3,z4,z27,z451,z6]),(0,[z7,z2,z3,z4,z5,z6,z565]),(0,[z7,z26,z2,z127,z4,z5,z6]),(0,[z7,z2,z3,z4,z566,z5,z6])],[(0,[z7,z2,z3,z4,z5,z567,z6]),(0,[z7,z2,z3,z4,z48,z27,z6]),(0,[z7,z2,z3,z4,z5,z6,z568]),(1,[z7,z2,z18,z4,z5,z19]),(0,[z7,z2,z3,z4,z5,z19,z21]),(0,[z7,z2,z36,z3,z4,z78,z6]),(0,[z7,z2,z3,z4,z5,z6,z569])],[(0,[z52,z7,z65,z3,z4,z5,z6]),(0,[z7,z2,z570,z3,z4,z5,z6]),(0,[z571,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z127,z3,z48,z5,z6]),(0,[z7,z2,z3,z4,z5,z572,z6])],[(0,[z7,z2,z573,z3,z4,z5,z6]),(0,[z7,z2,z140,z3,z4,z5,z6]),(0,[z54,z7,z2,z3,z4,z27,z6]),(0,[z7,z2,z3,z4,z27,z20,z6]),(0,[z7,z2,z3,z4,z5,z6,z574]),(0,[z7,z2,z3,z4,z575,z5,z6]),(0,[z7,z2,z3,z4,z5,z295,z6]),(0,[z7,z2,z3,z4,z5,z576,z6]),(0,[z7,z2,z3,z4,z78,z5,z6])],[(0,[z7,z2,z3,z577,z4,z5,z6]),(0,[z1,z9,z2,z3,z4,z5,z6]),(0,[z1,z7,z2,z3,z4,z5,z221]),(0,[z7,z578,z2,z3,z4,z5,z6]),(0,[z7,z14,z2,z3,z4,z17,z6]),(0,[z490,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z36,z3,z105,z5,z6])],[(0,[z7,z579,z2,z3,z4,z5,z6]),(0,[z108,z7,z2,z3,z4,z5,z6]),(0,[z125,z7,z2,z364,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z580]),(0,[z581,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z582,z6]),(0,[z7,z2,z3,z583,z4,z5,z6]),(0,[z584,z7,z2,z3,z4,z5,z6])]],
   [[(0,[z150,z7,z2,z3,z4,z27,z6]),(0,[z2,z63,z3,z46,z4,z5,z6]),(0,[z54,z236,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z585,z6]),(0,[z7,z2,z3,z4,z5,z586,z6]),(0,[z7,z2,z587,z3,z4,z5,z6]),(0,[z111,z7,z2,z3,z4,z12,z6])],[(0,[z7,z2,z3,z4,z231,z5,z6]),(0,[z7,z2,z127,z61,z4,z5,z6]),(0,[z7,z2,z77,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z588,z6])],[(0,[z7,z2,z3,z589,z4,z5,z6]),(0,[z7,z294,z2,z18,z4,z5,z6])],[(0,[z590,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z151,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z591]),(0,[z7,z2,z592,z3,z4,z5,z6]),(0,[z7,z2,z97,z4,z5,z6,z19]),(0,[z7,z2,z3,z4,z208,z5,z6])],[(1,[z7,z14,z97,z4,z5,z6]),(1,[z7,z2,z140,z4,z5,z6]),(0,[z7,z2,z237,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z5,z6,z593])],[(0,[z52,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z10,z109,z5,z6]),(0,[z7,z14,z2,z3,z4,z27,z6]),(0,[z7,z2,z3,z4,z382,z5,z6]),(0,[z7,z2,z3,z4,z5,z594,z6])],[(0,[z7,z294,z2,z97,z4,z5,z6]),(0,[z7,z2,z237,z3,z4,z5,z20])]],
   [[(0,[z595,z7,z2,z3,z4,z5,z6]),(0,[z9,z2,z120,z3,z4,z5,z6]),(0,[z7,z2,z3,z596,z4,z5,z6]),(0,[z7,z2,z3,z4,z27,z6,z19]),(0,[z7,z2,z3,z4,z340,z6,z21])],[(1,[z7,z2,z3,z4,z5,z168]),(0,[z7,z2,z3,z4,z5,z6,z369]),(0,[z7,z2,z3,z4,z597,z17,z6]),(0,[z7,z2,z3,z4,z5,z598,z6]),(0,[z7,z199,z2,z3,z4,z5,z6]),(0,[z7,z2,z599,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z184,z6]),(0,[z600,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z601,z3,z4,z5,z6]),(0,[z111,z7,z2,z3,z4,z17,z6]),(0,[z7,z2,z602,z3,z4,z5,z6]),(0,[z7,z2,z127,z3,z4,z5,z6])],[(0,[z23,z2,z3,z69,z4,z5,z6]),(0,[z7,z603,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z13,z6]),(0,[z562,z2,z3,z61,z4,z5,z6]),(0,[z7,z2,z3,z28,z47,z5,z6]),(0,[z7,z2,z604,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z605,z5,z6]),(0,[z7,z2,z3,z4,z78,z12,z5])],[(0,[z23,z7,z2,z46,z4,z5,z6]),(0,[z7,z161,z2,z3,z4,z529,z6]),(0,[z16,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z606,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z607,z5,z6]),(0,[z7,z2,z3,z4,z5,z194,z6]),(0,[z7,z2,z237,z3,z4,z27,z6])],[(0,[z608,z7,z2,z3,z4,z5,z6]),(0,[z609,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z118,z4,z5,z6])],[(0,[z610,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z61,z4,z5,z6,z19]),(0,[z7,z611,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z524,z4,z5,z6]),(0,[z7,z2,z3,z612,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z613,z6])]],
   [[(0,[z7,z2,z3,z614,z4,z5,z6]),(0,[z40,z7,z2,z3,z4,z145,z6]),(0,[z54,z7,z2,z3,z4,z5,z275]),(0,[z615,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z452,z3,z4,z5,z27]),(0,[z7,z2,z3,z4,z526,z5,z6]),(0,[z7,z2,z3,z4,z5,z616,z6]),(0,[z7,z2,z3,z617,z4,z5,z6])],[(0,[z7,z2,z63,z3,z4,z5,z6]),(0,[z23,z7,z2,z3,z4,z17,z6]),(0,[z7,z2,z120,z61,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z618,z6]),(0,[z7,z2,z61,z4,z48,z5,z6]),(0,[z7,z2,z3,z619,z4,z5,z6]),(0,[z7,z2,z3,z4,z620,z5,z6]),(0,[z7,z2,z621,z3,z4,z5,z6]),(1,[z7,z2,z237,z3,z5,z20]),(0,[z7,z2,z3,z622,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z623,z6]),(0,[z7,z26,z2,z3,z4,z5,z304]),(0,[z7,z2,z3,z4,z5,z71,z6])],[(0,[z7,z2,z3,z4,z5,z39,z21]),(0,[z7,z2,z3,z4,z5,z243,z6]),(0,[z624,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z237,z3,z5,z20,z6])],[(0,[z625,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z80])],[(0,[z7,z2,z626,z3,z4,z5,z6]),(1,[z98,z2,z3,z10,z5,z6]),(0,[z98,z2,z3,z4,z10,z5,z6])],[(0,[z7,z2,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z627,z5,z6]),(0,[z23,z2,z3,z4,z5,z13,z6]),(0,[z7,z2,z3,z4,z628,z5,z6]),(0,[z7,z2,z3,z4,z17,z6,z83]),(0,[z125,z7,z2,z3,z388,z5,z6]),(0,[z7,z2,z3,z629,z4,z5,z6])],[(1,[z7,z2,z3,z4,z488,z6]),(0,[z7,z2,z452,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z78,z17,z6]),(0,[z7,z2,z3,z4,z5,z6,z630])]],
   [[(0,[z7,z2,z3,z4,z5,z6,z631]),(0,[z7,z2,z3,z4,z17,z343,z6]),(0,[z7,z26,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z632,z4,z5,z6]),(0,[z23,z7,z2,z3,z4,z27,z6]),(0,[z7,z2,z633,z3,z4,z5,z6]),(0,[z7,z199,z2,z3,z4,z103,z6])],[(0,[z7,z2,z3,z296,z4,z5,z6]),(0,[z7,z65,z2,z3,z4,z488,z6]),(0,[z7,z634,z2,z3,z4,z5,z6]),(0,[z7,z2,z120,z3,z4,z5,z6]),(0,[z7,z2,z3,z69,z4,z17,z6]),(0,[z0,z2,z3,z4,z5,z13,z6]),(0,[z125,z7,z2,z3,z4,z5,z80])],[(0,[z7,z2,z3,z4,z635,z5,z6]),(0,[z7,z2,z3,z4,z636,z5,z6]),(0,[z7,z2,z3,z28,z109,z5,z6]),(0,[z7,z2,z3,z4,z5,z80,z21]),(0,[z7,z2,z637,z3,z4,z5,z6]),(0,[z7,z2,z638,z3,z4,z5,z6])],[(0,[z150,z7,z63,z3,z4,z5,z6]),(0,[z23,z2,z63,z3,z4,z5,z6]),(0,[z65,z2,z120,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z639,z6]),(0,[z7,z2,z3,z4,z48,z5,z6])],[(0,[z54,z7,z161,z3,z4,z5,z6]),(1,[z54,z7,z3,z109,z5,z6]),(0,[z7,z2,z640,z3,z4,z5,z6]),(0,[z641,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z167,z5,z295,z6])],[(0,[z9,z52,z2,z3,z4,z5,z6]),(0,[z7,z14,z2,z61,z4,z5,z6]),(0,[z54,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z17,z295,z6])],[(1,[z7,z2,z3,z4,z231,z6]),(0,[z7,z2,z3,z4,z5,z642,z6]),(0,[z7,z2,z3,z4,z5,z643,z6]),(0,[z7,z2,z3,z4,z78,z27,z6]),(0,[z7,z644,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z63,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z4,z99,z6]),(0,[z7,z2,z77,z3,z4,z5,z38]),(0,[z7,z41,z2,z3,z4,z5,z6]),(0,[z54,z7,z2,z3,z4,z5,z130]),(0,[z7,z2,z3,z4,z5,z6,z645]),(0,[z7,z2,z3,z4,z5,z6,z429]),(0,[z7,z646,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z340,z5,z6]),(0,[z7,z2,z3,z4,z647,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6,z648]),(0,[z7,z2,z3,z4,z5,z6,z649]),(0,[z1,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z650,z6]),(0,[z7,z199,z2,z3,z4,z375,z6]),(0,[z7,z651,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z652,z4,z5,z6]),(0,[z7,z2,z3,z653,z4,z5,z6])],[(0,[z7,z654,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z69,z4,z27,z6]),(0,[z7,z2,z3,z655,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z656]),(0,[z7,z2,z102,z3,z4,z17,z6])],[(0,[z7,z2,z3,z47,z4,z17,z6]),(0,[z657,z7,z2,z3,z4,z5,z6]),(0,[z75,z7,z2,z3,z4,z27,z6]),(0,[z7,z2,z37,z3,z4,z343,z6])],[(0,[z7,z115,z2,z3,z4,z17,z6]),(0,[z290,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z658,z6])],[(0,[z7,z659,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z47,z10,z5,z6]),(0,[z2,z3,z69,z4,z5,z6,z83]),(0,[z7,z2,z3,z4,z660,z5,z6]),(0,[z7,z2,z661,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z27,z6,z83]),(0,[z7,z2,z3,z662,z4,z5,z6]),(1,[z562,z2,z3,z4,z5,z6]),(0,[z7,z161,z2,z3,z47,z5,z6]),(0,[z7,z2,z3,z4,z27,z6,z555]),(0,[z7,z2,z3,z4,z663,z5,z6]),(0,[z7,z2,z3,z4,z5,z664,z6])],[(0,[z7,z65,z2,z3,z4,z466,z6]),(0,[z665,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z666,z6]),(0,[z7,z667,z2,z3,z4,z5,z6]),(0,[z7,z14,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z668])]],
   [[(0,[z669,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z670,z5,z6]),(0,[z7,z2,z3,z4,z27,z343,z6]),(0,[z7,z2,z3,z4,z136,z17,z6]),(0,[z671,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z672,z6]),(0,[z7,z2,z673,z3,z4,z5,z6]),(0,[z0,z2,z120,z3,z4,z5,z6]),(0,[z7,z2,z674,z3,z4,z5,z6]),(0,[z7,z2,z3,z675,z4,z5,z6])],[(0,[z7,z2,z676,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z38,z6,z83]),(0,[z7,z2,z3,z4,z17,z598,z6]),(0,[z7,z199,z2,z3,z4,z5,z80]),(1,[z318,z2,z3,z4,z5,z6]),(0,[z111,z7,z2,z36,z3,z4,z6]),(0,[z7,z677,z2,z3,z4,z5,z6]),(0,[z7,z678,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6,z168]),(0,[z7,z2,z63,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z679,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z680]),(0,[z7,z2,z3,z47,z4,z27,z6]),(0,[z7,z2,z110,z3,z4,z27,z6])],[(0,[z7,z2,z3,z681,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z682,z6]),(0,[z7,z2,z3,z4,z17,z13,z6]),(0,[z7,z2,z3,z4,z5,z83,z80]),(0,[z683,z7,z2,z3,z4,z5,z6])],[(0,[z684,z7,z2,z3,z4,z5,z6]),(0,[z0,z223,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z27,z295,z6]),(0,[z7,z2,z3,z4,z5,z685,z6]),(0,[z7,z2,z237,z3,z4,z5,z6])],[(0,[z7,z7,z2,z3,z4,z5,z6]),(0,[z686,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z687,z4,z5,z6]),(0,[z7,z2,z3,z688,z4,z5,z6])]],
   [[(0,[z689,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z690,z3,z4,z5,z6]),(0,[z7,z691,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z692,z5,z6]),(0,[z54,z7,z2,z179,z4,z5,z6]),(0,[z7,z2,z3,z4,z643,z27,z6]),(0,[z7,z2,z3,z4,z5,z20,z80])],[(0,[z9,z2,z3,z69,z4,z5,z6]),(0,[z7,z2,z3,z146,z4,z5,z6]),(0,[z7,z2,z3,z693,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z694,z6]),(0,[z7,z2,z3,z4,z5,z6,z695]),(0,[z7,z2,z3,z4,z696,z5,z6])],[(0,[z150,z32,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z697,z4,z5,z6]),(0,[z7,z2,z3,z4,z698,z5,z6]),(1,[z152,z2,z3,z4,z13,z6]),(0,[z7,z699,z2,z3,z4,z5,z6]),(0,[z54,z70,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z597,z5,z6])],[(0,[z7,z2,z63,z3,z4,z27,z6]),(0,[z7,z2,z3,z700,z4,z5,z6]),(0,[z7,z2,z3,z701,z4,z5,z6]),(0,[z7,z2,z3,z4,z55,z5,z6]),(0,[z7,z2,z3,z4,z176,z17,z6]),(0,[z7,z2,z3,z4,z17,z71,z6]),(0,[z111,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z702,z3,z4,z5,z6]),(0,[z7,z2,z37,z3,z4,z12,z6])],[(0,[z7,z2,z703,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z8,z6]),(0,[z7,z2,z3,z109,z5,z6,z21]),(0,[z7,z2,z3,z4,z17,z6,z80]),(0,[z7,z2,z3,z4,z704,z5,z6]),(0,[z7,z2,z36,z3,z4,z295,z6])],[(0,[z705,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z46,z4,z17,z6]),(0,[z7,z161,z2,z3,z109,z5,z6]),(0,[z111,z7,z2,z3,z4,z147,z6]),(0,[z7,z2,z3,z4,z147,z5,z6])],[(1,[z7,z2,z3,z4,z5,z216]),(0,[z9,z7,z2,z3,z4,z17,z6]),(0,[z7,z706,z2,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z2,z3,z4,z707,z13,z6]),(0,[z16,z2,z3,z4,z13,z6]),(0,[z7,z2,z708,z3,z4,z6]),(0,[z7,z2,z3,z709,z5,z6]),(0,[z7,z2,z3,z710,z5,z6]),(0,[z2,z3,z711,z4,z5,z6]),(0,[z7,z2,z237,z3,z5,z20])],[(0,[z7,z2,z712,z4,z5,z6]),(0,[z7,z2,z3,z296,z184,z6]),(0,[z7,z2,z3,z4,z713,z6]),(0,[z108,z2,z3,z69,z5,z6]),(0,[z7,z2,z3,z4,z17,z34]),(0,[z113,z2,z3,z4,z145,z6]),(0,[z35,z2,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z382,z714]),(0,[z7,z2,z4,z5,z715,z19])],[(0,[z41,z2,z3,z4,z17,z6]),(0,[z40,z7,z61,z4,z17,z6]),(0,[z2,z3,z4,z716,z5,z6]),(0,[z94,z2,z3,z4,z12,z5]),(0,[z7,z2,z3,z717,z5,z6]),(0,[z7,z2,z3,z4,z718,z6])],[(0,[z7,z2,z3,z4,z719,z6]),(0,[z720,z2,z3,z4,z5,z6]),(0,[z7,z2,z179,z4,z79,z6]),(0,[z2,z3,z4,z721,z5,z6]),(0,[z7,z2,z3,z4,z5,z722])],[(0,[z7,z2,z3,z4,z723,z6]),(0,[z7,z2,z3,z4,z724,z6]),(0,[z7,z2,z3,z4,z5,z725]),(0,[z98,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z4,z726,z6]),(0,[z2,z3,z4,z211,z727,z5]),(0,[z2,z3,z4,z727,z5,z6]),(0,[z728,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z729,z6])],[(0,[z7,z2,z3,z4,z27,z216]),(0,[z70,z2,z3,z4,z79,z6])],[(0,[z7,z2,z3,z4,z730,z6]),(0,[z7,z14,z97,z4,z15,z6]),(0,[z7,z2,z3,z146,z4,z211]),(0,[z94,z2,z3,z4,z116,z6]),(0,[z731,z2,z66,z3,z4,z6]),(0,[z7,z2,z732,z3,z4,z6])],[(0,[z7,z2,z90,z4,z184,z6]),(0,[z7,z2,z3,z4,z733,z6]),(0,[z7,z2,z3,z734,z5,z6]),(0,[z16,z2,z3,z4,z17,z6]),(0,[z16,z2,z3,z4,z176,z6]),(0,[z735,z2,z3,z4,z375,z6])]],
   [[(0,[z52,z65,z3,z4,z17,z6]),(0,[z7,z380,z3,z4,z27,z6]),(0,[z7,z2,z3,z4,z211,z116]),(0,[z2,z3,z4,z5,z736,z6])],[(0,[z7,z2,z3,z4,z184,z6]),(0,[z32,z2,z3,z4,z5,z168]),(0,[z7,z2,z3,z4,z27,z34]),(0,[z7,z2,z3,z4,z737,z6]),(0,[z7,z2,z3,z4,z738,z6]),(0,[z7,z2,z3,z4,z739,z5]),(0,[z35,z2,z3,z4,z27,z6]),(0,[z7,z2,z171,z4,z5,z19]),(0,[z2,z36,z280,z3,z295,z6]),(0,[z7,z2,z3,z50,z5,z20])],[(0,[z7,z2,z3,z4,z740,z6]),(0,[z7,z2,z3,z4,z741,z6])],[(0,[z7,z2,z3,z4,z742,z6]),(0,[z743,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z17,z304]),(0,[z164,z2,z3,z4,z12,z149])],[(0,[z7,z2,z90,z4,z231,z6]),(0,[z108,z2,z3,z4,z5,z6]),(0,[z9,z2,z3,z69,z5,z6]),(0,[z2,z3,z84,z4,z17,z6]),(0,[z54,z7,z3,z109,z5,z6]),(0,[z7,z2,z3,z4,z744,z6]),(0,[z745,z2,z3,z4,z211,z27]),(0,[z7,z2,z3,z4,z17,z86]),(0,[z7,z2,z3,z4,z746,z6]),(0,[z125,z7,z126,z4,z5,z80])],[(0,[z7,z2,z3,z4,z17,z747])],[(0,[z7,z2,z3,z4,z231,z6]),(0,[z7,z2,z3,z4,z748,z6]),(0,[z2,z3,z749,z4,z5,z6]),(0,[z236,z2,z3,z4,z5,z275]),(0,[z94,z2,z3,z4,z17,z6]),(0,[z750,z2,z3,z4,z5,z6]),(0,[z751,z2,z3,z4,z5,z6])],[(0,[z2,z749,z46,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z752]),(0,[z2,z528,z3,z10,z5,z6]),(0,[z2,z3,z4,z208,z5,z6]),(0,[z0,z2,z3,z4,z17,z38]),(0,[z7,z2,z3,z4,z5,z753]),(0,[z754,z2,z3,z4,z5,z6]),(0,[z755,z2,z3,z4,z5,z6]),(0,[z7,z347,z3,z4,z27,z6]),(0,[z7,z2,z756,z3,z27,z6]),(0,[z7,z2,z3,z4,z757,z6]),(0,[z111,z7,z2,z4,z423,z6]),(0,[z2,z3,z4,z5,z399,z758])]],
   [[(0,[z52,z65,z3,z4,z27,z6]),(0,[z2,z255,z97,z4,z5,z6]),(0,[z54,z3,z190,z109,z5,z6]),(0,[z2,z3,z759,z4,z5,z6])],[(0,[z7,z2,z3,z760,z5,z6]),(0,[z7,z2,z3,z761,z5,z6]),(0,[z7,z2,z3,z4,z211,z149]),(0,[z745,z2,z3,z4,z211,z5]),(0,[z7,z433,z3,z4,z5,z39]),(0,[z7,z2,z18,z4,z220,z19]),(0,[z7,z2,z3,z5,z762,z21])],[(0,[z2,z3,z4,z5,z86,z763])],[(0,[z65,z764,z3,z4,z5,z6]),(0,[z7,z2,z3,z765,z5,z6]),(0,[z766,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z5,z767,z6]),(0,[z7,z2,z3,z4,z5,z768]),(0,[z745,z2,z3,z4,z27,z6]),(0,[z2,z3,z4,z17,z87,z6])],[(0,[z2,z3,z363,z5,z13,z6]),(0,[z150,z63,z3,z4,z184,z6]),(0,[z2,z3,z84,z4,z27,z6]),(0,[z7,z2,z3,z4,z27,z86]),(0,[z2,z769,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z243,z39]),(0,[z2,z280,z3,z4,z78,z6]),(0,[z2,z3,z4,z432,z770,z6]),(0,[z7,z2,z3,z4,z771,z6])],[(0,[z23,z2,z120,z4,z5,z6]),(0,[z7,z483,z3,z4,z17,z6]),(0,[z7,z2,z140,z4,z55,z6]),(0,[z7,z2,z3,z105,z206,z6]),(0,[z7,z2,z127,z28,z17,z6]),(0,[z7,z2,z599,z48,z5,z6])],[(0,[z7,z2,z3,z4,z772,z6]),(0,[z164,z2,z3,z4,z13,z6]),(0,[z1,z2,z3,z4,z99,z6]),(0,[z7,z3,z4,z773,z27,z6]),(0,[z94,z2,z3,z4,z27,z6])],[(0,[z7,z2,z3,z4,z5,z774]),(0,[z0,z2,z3,z4,z27,z38]),(0,[z7,z3,z761,z109,z5,z6]),(0,[z7,z2,z3,z4,z5,z775]),(0,[z7,z2,z4,z5,z776,z6]),(0,[z7,z2,z3,z777,z5,z6])]],
   [[(0,[z51,z2,z3,z10,z5,z6]),(0,[z1,z2,z3,z4,z643,z6]),(0,[z7,z2,z3,z4,z778,z6]),(0,[z2,z779,z3,z4,z5,z6])],[(0,[z2,z3,z118,z4,z5,z6]),(0,[z780,z2,z3,z4,z5,z6]),(0,[z7,z538,z3,z4,z27,z6]),(0,[z7,z2,z3,z4,z132,z20])],[(0,[z0,z2,z3,z4,z99,z38]),(0,[z7,z26,z2,z48,z27,z6]),(0,[z7,z3,z327,z4,z27,z6])],[(0,[z7,z2,z3,z4,z5,z781]),(0,[z7,z2,z3,z4,z27,z782]),(0,[z7,z2,z36,z3,z783,z6])],[(0,[z7,z2,z3,z363,z184,z6]),(0,[z150,z63,z3,z4,z17,z6]),(0,[z150,z528,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z784,z6]),(0,[z7,z2,z3,z785,z5,z6]),(0,[z2,z3,z69,z786,z5,z6]),(0,[z7,z2,z77,z3,z4,z435])],[(0,[z7,z2,z127,z28,z27,z6]),(0,[z7,z2,z3,z4,z27,z787]),(0,[z164,z2,z3,z4,z17,z6]),(0,[z788,z2,z3,z4,z5,z6]),(1,[z7,z2,z4,z789,z6]),(0,[z7,z2,z4,z5,z715,z6]),(0,[z790,z2,z3,z4,z5,z6])],[(0,[z2,z120,z68,z4,z5,z6]),(0,[z7,z2,z3,z4,z791,z6]),(0,[z7,z2,z3,z4,z792,z6]),(0,[z236,z2,z3,z4,z5,z130]),(0,[z54,z7,z179,z109,z5,z6]),(0,[z7,z2,z3,z4,z793,z6]),(0,[z7,z3,z4,z5,z39,z794]),(0,[z7,z2,z3,z4,z382,z795]),(0,[z7,z2,z3,z4,z796,z6])],[(0,[z108,z2,z3,z363,z5,z6]),(0,[z7,z2,z3,z4,z797,z6]),(0,[z7,z2,z798,z4,z5,z6]),(0,[z2,z3,z4,z5,z458,z83]),(0,[z7,z2,z3,z4,z12,z293]),(0,[z7,z2,z3,z4,z799,z6]),(0,[z7,z3,z4,z27,z6,z300]),(0,[z800,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z801,z3,z5,z6]),(0,[z7,z2,z97,z4,z5,z369]),(0,[z7,z2,z127,z139,z5,z6])],[(0,[z7,z2,z3,z802,z5,z6]),(0,[z7,z2,z3,z4,z5,z803]),(0,[z23,z2,z338,z4,z5,z6]),(0,[z7,z2,z804,z3,z4,z6])],[(0,[z41,z2,z61,z4,z5,z6]),(0,[z7,z2,z3,z92,z5,z242]),(0,[z671,z7,z61,z4,z5,z6]),(0,[z7,z2,z379,z3,z5,z20]),(1,[z7,z2,z3,z4,z805])],[(0,[z2,z120,z90,z4,z5,z6]),(0,[z806,z2,z3,z4,z5,z6]),(0,[z259,z7,z3,z109,z5,z6]),(0,[z7,z2,z3,z4,z27,z807]),(0,[z2,z3,z4,z27,z87,z6])],[(0,[z7,z2,z90,z4,z5,z216]),(0,[z75,z2,z3,z4,z13,z6]),(0,[z7,z2,z3,z4,z808,z6]),(0,[z7,z3,z4,z211,z17,z27])],[(0,[z7,z2,z3,z4,z809,z6]),(0,[z2,z3,z4,z99,z13,z6]),(0,[z7,z3,z4,z761,z5,z6]),(0,[z164,z2,z3,z4,z27,z6]),(0,[z125,z35,z3,z4,z5,z80]),(0,[z810,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z216]),(0,[z9,z2,z3,z69,z17,z6]),(0,[z108,z2,z3,z4,z17,z6]),(0,[z811,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z812]),(0,[z7,z2,z3,z4,z5,z813]),(0,[z125,z7,z3,z4,z647,z5]),(0,[z814,z2,z3,z4,z5,z6])]],
   [[(0,[z465,z2,z3,z4,z5,z83]),(0,[z7,z115,z3,z4,z211,z27]),(0,[z7,z2,z36,z3,z4,z211]),(0,[z486,z2,z3,z4,z59,z6]),(0,[z7,z2,z4,z147,z789,z6])],[(0,[z98,z2,z90,z4,z5,z6]),(0,[z2,z673,z3,z69,z5,z6]),(0,[z98,z2,z3,z670,z5,z6]),(0,[z815,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z105,z783,z6])],[(0,[z35,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z816,z5,z6]),(0,[z23,z2,z749,z4,z5,z6]),(0,[z609,z2,z3,z69,z5,z6]),(0,[z7,z2,z3,z4,z5,z34]),(0,[z2,z3,z4,z73,z707,z6]),(0,[z7,z2,z817,z3,z4,z6]),(0,[z44,z2,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z5,z714]),(0,[z7,z2,z3,z105,z487,z6])],[(0,[z7,z2,z151,z4,z5,z168]),(0,[z41,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z818,z6]),(0,[z7,z2,z3,z4,z5,z819]),(0,[z7,z2,z25,z3,z4,z78]),(0,[z40,z7,z61,z4,z5,z6]),(0,[z7,z2,z3,z4,z820,z6]),(0,[z7,z2,z3,z4,z12,z407])],[(0,[z7,z2,z821,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z275]),(0,[z7,z2,z822,z3,z4,z27]),(0,[z7,z49,z3,z4,z17,z6]),(0,[z823,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z824,z5,z6]),(0,[z7,z2,z825,z4,z5,z6]),(0,[z54,z7,z3,z109,z55,z6]),(0,[z157,z3,z4,z17,z59,z6]),(0,[z7,z2,z3,z4,z17,z826]),(0,[z7,z2,z4,z5,z789,z6]),(0,[z7,z2,z3,z4,z12,z112]),(0,[z827,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z12,z5,z87])],[(0,[z7,z2,z3,z4,z5,z828]),(0,[z9,z2,z3,z69,z27,z6]),(0,[z7,z2,z3,z4,z829,z6]),(0,[z108,z2,z3,z4,z27,z6]),(0,[z7,z2,z3,z4,z830,z6]),(0,[z7,z2,z452,z3,z4,z430]),(0,[z2,z3,z4,z831,z17,z6]),(0,[z7,z3,z4,z5,z6,z794]),(0,[z7,z2,z4,z832,z5,z6])],[(0,[z2,z833,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z834]),(0,[z7,z2,z3,z4,z835,z6])]],
   [[(0,[z7,z2,z90,z296,z5,z6]),(0,[z16,z2,z3,z4,z5,z6]),(0,[z290,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z707,z5,z6]),(0,[z7,z2,z4,z836,z5,z6]),(0,[z40,z41,z61,z4,z5,z6]),(0,[z7,z2,z3,z4,z837,z6]),(0,[z2,z3,z4,z838,z5,z6]),(0,[z7,z2,z839,z4,z5,z6]),(0,[z119,z2,z3,z4,z17,z6]),(0,[z35,z2,z364,z4,z5,z6]),(0,[z7,z2,z127,z832,z5,z6]),(0,[z7,z2,z3,z652,z5,z21])],[(0,[z52,z65,z3,z4,z5,z6]),(0,[z7,z2,z822,z3,z4,z5]),(0,[z65,z3,z4,z660,z5,z6]),(0,[z7,z2,z3,z4,z17,z221]),(0,[z7,z2,z840,z4,z5,z6]),(0,[z2,z3,z4,z208,z27,z6]),(0,[z16,z2,z3,z4,z17,z841]),(0,[z2,z3,z4,z5,z6,z763])],[(0,[z7,z2,z3,z296,z5,z6]),(0,[z1,z2,z90,z4,z5,z6]),(0,[z0,z2,z3,z4,z8,z38]),(0,[z842,z2,z3,z4,z5,z6]),(0,[z2,z77,z3,z4,z5,z243])],[(0,[z7,z2,z3,z843,z5,z6]),(0,[z7,z2,z3,z4,z844,z5]),(0,[z2,z3,z4,z15,z845,z6]),(0,[z7,z2,z3,z4,z846,z6]),(0,[z7,z2,z3,z4,z773,z6]),(0,[z7,z2,z110,z3,z213,z6]),(0,[z7,z2,z452,z3,z4,z211])],[(0,[z7,z2,z3,z4,z847,z6]),(0,[z7,z2,z3,z848,z5,z6]),(0,[z2,z3,z4,z5,z849,z83]),(0,[z7,z2,z3,z303,z5,z6]),(0,[z745,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z304]),(0,[z290,z2,z127,z28,z5,z6]),(0,[z7,z2,z77,z3,z4,z220])],[(0,[z2,z3,z84,z4,z5,z6]),(0,[z7,z2,z3,z4,z850,z6]),(0,[z2,z3,z4,z5,z851,z6]),(0,[z7,z199,z398,z3,z4,z5]),(0,[z7,z2,z3,z4,z5,z852]),(0,[z7,z2,z3,z5,z783,z6])],[(0,[z351,z63,z3,z4,z5,z6]),(0,[z2,z172,z3,z4,z13,z6]),(0,[z7,z2,z3,z853,z5,z6]),(0,[z236,z2,z3,z4,z17,z6]),(0,[z2,z769,z3,z4,z27,z6]),(0,[z7,z2,z3,z303,z117,z6])],[(0,[z23,z2,z120,z4,z27,z6]),(0,[z7,z2,z3,z92,z5,z369]),(0,[z7,z2,z3,z4,z854,z6]),(0,[z7,z2,z77,z3,z4,z805])]],
   [[(0,[z2,z120,z3,z363,z5,z6]),(0,[z0,z2,z3,z4,z5,z38]),(0,[z855,z2,z3,z4,z5,z6]),(0,[z7,z2,z856,z4,z5,z6]),(0,[z119,z2,z3,z4,z27,z6])],[(0,[z52,z2,z90,z4,z5,z6]),(0,[z7,z2,z3,z363,z5,z216]),(0,[z7,z2,z3,z4,z27,z221]),(0,[z7,z2,z3,z4,z857,z6]),(0,[z7,z2,z3,z4,z27,z775]),(0,[z111,z7,z2,z3,z4,z211]),(0,[z7,z2,z3,z148,z17,z21])],[(0,[z7,z2,z3,z858,z5,z6]),(0,[z7,z2,z3,z4,z859,z6]),(0,[z98,z2,z3,z557,z5,z6]),(0,[z7,z2,z3,z4,z860,z6]),(0,[z7,z2,z359,z3,z4,z211]),(0,[z861,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z862]),(0,[z150,z764,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z38,z849]),(0,[z2,z3,z118,z4,z27,z6]),(0,[z7,z2,z3,z4,z17,z841]),(0,[z7,z2,z3,z148,z5,z762])],[(0,[z113,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z863,z6]),(0,[z7,z2,z3,z4,z5,z782]),(0,[z7,z2,z3,z4,z864,z6]),(0,[z7,z2,z3,z4,z865,z6]),(0,[z866,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z130]),(0,[z7,z2,z3,z4,z117,z6]),(0,[z7,z2,z3,z4,z867,z6])],[(0,[z150,z63,z3,z296,z5,z6]),(0,[z2,z3,z4,z488,z59,z6]),(0,[z7,z2,z868,z4,z5,z6]),(0,[z7,z129,z3,z4,z27,z6]),(0,[z94,z2,z364,z4,z5,z6]),(0,[z7,z2,z3,z612,z5,z21]),(0,[z2,z3,z4,z5,z758,z6])],[(0,[z98,z2,z3,z363,z5,z6]),(0,[z7,z2,z3,z4,z869,z6]),(0,[z7,z2,z3,z4,z5,z787]),(0,[z236,z2,z3,z4,z27,z6]),(0,[z7,z2,z179,z4,z5,z275]),(0,[z7,z2,z870,z3,z4,z529]),(0,[z7,z2,z3,z4,z871,z6]),(0,[z7,z2,z127,z28,z5,z6]),(0,[z872,z2,z3,z4,z5,z6])],[(0,[z7,z2,z873,z4,z5,z6]),(0,[z7,z2,z3,z4,z17,z141]),(0,[z7,z2,z3,z4,z874,z6]),(0,[z7,z2,z3,z4,z12,z180]),(0,[z7,z2,z77,z3,z4,z78])]],
   [[(0,[z7,z2,z3,z875,z5,z6]),(0,[z54,z7,z140,z109,z5,z6]),(0,[z2,z3,z4,z190,z17,z6]),(0,[z7,z677,z3,z4,z5,z39]),(0,[z7,z2,z3,z4,z876,z6])],[(0,[z7,z2,z151,z4,z231,z6]),(0,[z877,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z878,z6]),(0,[z7,z202,z97,z4,z5,z6]),(0,[z879,z2,z3,z4,z5,z6]),(0,[z16,z2,z3,z4,z17,z880]),(0,[z457,z7,z3,z4,z5,z80]),(0,[z7,z2,z3,z4,z881,z6]),(0,[z2,z3,z4,z882,z5,z6])],[(0,[z65,z3,z4,z257,z5,z6]),(0,[z7,z2,z364,z4,z117,z6]),(0,[z7,z2,z3,z303,z12,z5]),(0,[z7,z2,z3,z4,z12,z149])],[(0,[z150,z63,z90,z4,z5,z6]),(0,[z883,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z884,z6]),(0,[z7,z2,z3,z4,z12,z516])],[(1,[z764,z3,z4,z5,z6]),(0,[z2,z120,z4,z5,z390,z6]),(0,[z7,z2,z3,z4,z5,z807])],[(0,[z150,z63,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z885,z6]),(0,[z886,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z887,z6]),(0,[z888,z2,z3,z4,z5,z6]),(0,[z889,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z231,z168]),(0,[z164,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z890,z6]),(0,[z891,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z17,z275]),(0,[z7,z2,z3,z4,z892,z6]),(1,[z7,z3,z4,z773,z6]),(0,[z7,z525,z3,z4,z27,z6]),(0,[z16,z2,z3,z4,z59,z6]),(0,[z7,z2,z3,z303,z116,z6]),(0,[z7,z2,z37,z3,z4,z399])],[(0,[z1,z2,z3,z363,z5,z6]),(0,[z2,z893,z3,z4,z5,z6]),(0,[z32,z2,z749,z4,z5,z6]),(0,[z7,z2,z3,z4,z27,z141]),(0,[z35,z2,z3,z388,z5,z6]),(0,[z894,z7,z2,z3,z4,z6])]],
   [[(0,[z895,z2,z3,z4,z5,z6])],[(0,[z7,z2,z896,z4,z5,z6]),(0,[z7,z2,z3,z897,z5,z6]),(0,[z7,z2,z898,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z899]),(0,[z41,z2,z3,z189,z5,z6]),(0,[z40,z7,z61,z189,z5,z6]),(0,[z7,z115,z3,z4,z773,z6]),(0,[z7,z2,z3,z4,z17,z180])],[(0,[z7,z2,z3,z900,z5,z6]),(0,[z7,z2,z3,z4,z901,z6]),(0,[z2,z120,z405,z4,z5,z6]),(0,[z7,z2,z3,z4,z902,z6]),(0,[z1,z2,z3,z4,z59,z6]),(0,[z903,z2,z3,z4,z5,z6]),(0,[z7,z2,z904,z4,z5,z6]),(0,[z290,z2,z3,z4,z17,z6]),(0,[z94,z2,z126,z4,z5,z6])],[(0,[z7,z2,z90,z363,z5,z6]),(0,[z2,z3,z4,z59,z5,z6]),(0,[z7,z2,z3,z786,z5,z6]),(0,[z905,z2,z3,z4,z5,z6]),(0,[z490,z2,z127,z28,z5,z6]),(0,[z7,z2,z3,z4,z5,z715])],[(0,[z7,z2,z3,z296,z17,z6]),(0,[z7,z2,z3,z4,z906,z6]),(0,[z7,z2,z3,z4,z116,z6]),(0,[z7,z2,z907,z3,z5,z6])],[(0,[z41,z2,z3,z4,z27,z6]),(0,[z40,z7,z61,z4,z27,z6]),(0,[z7,z2,z3,z4,z908,z6])],[(0,[z52,z2,z3,z363,z5,z6]),(0,[z7,z909,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z910]),(0,[z7,z2,z179,z4,z5,z130]),(0,[z7,z2,z3,z4,z27,z275]),(0,[z54,z7,z3,z761,z5,z6]),(0,[z7,z452,z3,z4,z17,z27]),(0,[z7,z2,z3,z303,z17,z6]),(0,[z7,z454,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z911,z6]),(0,[z7,z2,z3,z4,z912,z6])],[(0,[z7,z2,z3,z4,z194,z6]),(0,[z913,z2,z3,z4,z5,z6]),(0,[z44,z2,z36,z3,z295,z6])]],
   [[(0,[z764,z63,z3,z4,z5,z6]),(0,[z7,z2,z3,z914,z5,z6]),(0,[z7,z915,z61,z4,z5,z6]),(0,[z7,z2,z187,z3,z5,z20])],[(0,[z7,z2,z3,z4,z27,z180]),(0,[z7,z2,z3,z4,z5,z794])],[(0,[z7,z2,z90,z4,z17,z6]),(0,[z7,z2,z3,z4,z916,z6]),(0,[z2,z3,z4,z917,z5,z6]),(0,[z16,z2,z3,z4,z27,z6]),(0,[z290,z2,z3,z4,z27,z6]),(0,[z226,z7,z2,z4,z598,z6]),(0,[z731,z2,z3,z4,z5,z6]),(0,[z7,z2,z37,z4,z789,z6]),(0,[z7,z2,z918,z4,z5,z6])],[(0,[z95,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z919,z6]),(0,[z44,z2,z3,z4,z5,z6]),(0,[z920,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z921]),(0,[z111,z7,z2,z62,z4,z6])],[(0,[z7,z2,z3,z4,z17,z6]),(0,[z7,z2,z3,z296,z27,z6]),(0,[z7,z2,z3,z4,z922,z6]),(0,[z7,z2,z3,z4,z5,z923]),(0,[z94,z2,z3,z388,z5,z6]),(0,[z7,z2,z3,z4,z382,z6]),(0,[z924,z2,z3,z4,z5,z6])],[(0,[z2,z764,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z925]),(0,[z7,z2,z3,z4,z5,z926]),(0,[z7,z2,z3,z4,z211,z27]),(0,[z7,z3,z4,z453,z27,z6]),(0,[z7,z2,z3,z4,z17,z399]),(0,[z927,z2,z3,z4,z5,z6]),(0,[z2,z928,z3,z4,z5,z6]),(0,[z751,z2,z3,z4,z432,z6])],[(0,[z625,z2,z120,z4,z5,z6]),(0,[z113,z2,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z17,z130]),(0,[z7,z2,z3,z303,z27,z6]),(0,[z7,z2,z3,z4,z27,z304]),(0,[z7,z2,z3,z4,z5,z826]),(0,[z2,z3,z4,z5,z87,z80])],[(0,[z7,z2,z3,z929,z5,z6]),(0,[z9,z2,z3,z614,z5,z6]),(0,[z2,z3,z4,z831,z5,z6]),(0,[z7,z2,z3,z4,z930,z6])]],
   [[(0,[z150,z63,z3,z363,z5,z6]),(0,[z7,z2,z3,z931,z5,z6]),(0,[z94,z2,z3,z4,z5,z80])],[(0,[z7,z2,z151,z4,z5,z216]),(0,[z349,z63,z3,z4,z5,z6]),(0,[z119,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z932]),(0,[z2,z3,z4,z845,z5,z6]),(0,[z7,z3,z4,z27,z443,z6]),(0,[z7,z2,z3,z4,z17,z933]),(0,[z7,z2,z3,z388,z117,z6]),(0,[z2,z280,z3,z4,z12,z6])],[(0,[z7,z2,z90,z4,z27,z6]),(0,[z7,z2,z3,z4,z5,z221]),(0,[z934,z2,z3,z4,z5,z6]),(0,[z7,z2,z935,z4,z5,z6]),(0,[z7,z2,z3,z4,z211,z5]),(0,[z7,z2,z364,z4,z17,z6]),(0,[z16,z2,z3,z4,z5,z841]),(0,[z7,z2,z3,z4,z936,z304])],[(0,[z937,z2,z3,z4,z5,z6]),(0,[z7,z938,z3,z4,z5,z6]),(0,[z7,z2,z3,z5,z762,z6])],[(0,[z7,z2,z3,z4,z27,z6]),(0,[z7,z2,z3,z4,z939,z6]),(0,[z7,z2,z3,z277,z5,z21]),(0,[z7,z940,z2,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z941]),(0,[z7,z2,z3,z4,z942,z6])],[(0,[z7,z2,z3,z4,z5,z943]),(0,[z2,z63,z90,z4,z5,z6]),(0,[z2,z120,z3,z4,z5,z168]),(0,[z563,z2,z3,z4,z5,z83]),(0,[z40,z113,z61,z4,z5,z6])],[(0,[z319,z2,z3,z4,z5,z83]),(0,[z1,z2,z3,z4,z514,z6]),(0,[z113,z2,z3,z4,z27,z6]),(0,[z7,z2,z3,z4,z27,z130]),(0,[z7,z2,z944,z4,z5,z6]),(0,[z945,z2,z3,z4,z27,z6]),(0,[z7,z2,z3,z4,z211,z555]),(0,[z946,z2,z3,z4,z17,z6]),(0,[z7,z3,z4,z647,z17,z6]),(0,[z947,z2,z3,z4,z5,z6])],[(0,[z236,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z948,z6]),(0,[z7,z2,z3,z4,z99,z6]),(0,[z7,z2,z949,z4,z5,z6]),(0,[z7,z472,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z950,z6]),(0,[z7,z2,z36,z3,z4,z141])]],
   [[(0,[z7,z2,z3,z92,z145,z6]),(0,[z7,z2,z3,z189,z145,z6]),(0,[z7,z2,z3,z4,z5,z951])],[(0,[z2,z3,z69,z363,z5,z6]),(0,[z7,z2,z3,z4,z952,z6]),(0,[z2,z3,z4,z5,z243,z6]),(0,[z2,z3,z4,z78,z59,z6])],[(0,[z106,z7,z3,z4,z5,z80]),(0,[z7,z2,z3,z4,z5,z953]),(0,[z7,z97,z915,z4,z5,z6]),(0,[z954,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z955,z5,z6]),(0,[z7,z2,z3,z148,z5,z21])],[(0,[z7,z2,z3,z4,z5,z956]),(0,[z98,z2,z3,z4,z5,z168]),(0,[z2,z280,z3,z4,z17,z6]),(0,[z7,z3,z4,z5,z794,z80]),(0,[z7,z2,z336,z4,z5,z19]),(0,[z95,z2,z3,z4,z12,z6])],[(0,[z7,z2,z3,z4,z211,z73]),(0,[z7,z2,z3,z4,z957,z5]),(0,[z7,z2,z3,z4,z5,z958]),(0,[z7,z2,z3,z4,z959,z6]),(0,[z7,z2,z3,z4,z5,z841]),(1,[z7,z3,z4,z5,z794]),(0,[z7,z960,z3,z4,z5,z6])],[(0,[z164,z2,z3,z4,z5,z38]),(0,[z2,z3,z961,z4,z5,z6]),(0,[z7,z2,z962,z4,z5,z6])],[(0,[z2,z963,z3,z4,z5,z6]),(0,[z7,z2,z179,z4,z17,z6]),(0,[z7,z3,z4,z17,z502,z6])],[(0,[z7,z2,z3,z4,z964,z6]),(0,[z7,z2,z3,z363,z17,z6]),(0,[z150,z63,z3,z4,z27,z6]),(0,[z7,z2,z3,z4,z965,z6]),(0,[z152,z2,z3,z4,z59,z6]),(0,[z966,z2,z3,z4,z74,z6]),(0,[z7,z3,z653,z4,z27,z6]),(0,[z7,z3,z503,z4,z27,z6]),(0,[z2,z967,z3,z4,z17,z6]),(0,[z968,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z969]),(0,[z7,z2,z3,z4,z5,z970]),(0,[z2,z3,z287,z10,z5,z6]),(0,[z70,z2,z3,z4,z17,z6]),(0,[z7,z2,z140,z4,z79,z6]),(0,[z7,z2,z3,z524,z597,z6]),(0,[z7,z2,z3,z4,z5,z141]),(0,[z968,z2,z3,z4,z5,z399])],[(0,[z2,z3,z4,z190,z5,z6]),(0,[z971,z2,z3,z4,z5,z6]),(0,[z2,z3,z972,z4,z5,z6]),(0,[z7,z2,z3,z4,z973,z6]),(0,[z125,z7,z3,z4,z5,z794]),(0,[z7,z2,z3,z148,z340,z21])],[(0,[z7,z2,z3,z4,z957,z194]),(0,[z16,z2,z3,z4,z5,z880]),(0,[z7,z2,z18,z4,z132,z19]),(0,[z2,z3,z4,z12,z208,z149])],[(0,[z52,z550,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z974]),(0,[z2,z3,z4,z5,z975,z6]),(0,[z976,z2,z3,z4,z5,z6]),(0,[z7,z291,z3,z4,z17,z6])],[(0,[z1,z2,z3,z4,z5,z168]),(0,[z7,z2,z977,z4,z5,z6]),(0,[z2,z302,z3,z10,z5,z6]),(0,[z978,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z979,z27]),(0,[z16,z157,z3,z4,z17,z6]),(0,[z7,z2,z832,z48,z5,z6]),(0,[z7,z2,z3,z4,z5,z980]),(0,[z7,z2,z77,z3,z4,z340])],[(0,[z2,z3,z4,z5,z34,z83]),(0,[z981,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z59,z27,z6]),(0,[z95,z2,z3,z4,z17,z6]),(0,[z125,z7,z3,z303,z5,z80]),(0,[z7,z2,z3,z105,z4,z141])],[(0,[z7,z764,z3,z4,z5,z6]),(0,[z7,z2,z179,z4,z27,z6])],[(0,[z7,z2,z3,z363,z27,z6]),(0,[z52,z764,z3,z4,z5,z6]),(0,[z351,z7,z61,z4,z5,z6]),(0,[z152,z2,z3,z4,z707,z6]),(0,[z41,z2,z3,z4,z5,z242]),(0,[z40,z7,z61,z4,z5,z242]),(0,[z7,z2,z982,z4,z5,z6]),(0,[z7,z199,z3,z4,z17,z39]),(0,[z2,z3,z983,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z984]),(0,[z70,z2,z3,z4,z27,z6]),(0,[z7,z2,z77,z3,z4,z103]),(0,[z7,z2,z3,z4,z132,z21])],[(0,[z7,z2,z3,z4,z979,z5]),(1,[z2,z3,z4,z707,z6]),(0,[z7,z2,z3,z985,z5,z6]),(0,[z236,z2,z179,z4,z5,z6]),(0,[z7,z2,z3,z388,z17,z6]),(0,[z7,z986,z3,z4,z5,z6])],[(0,[z2,z63,z3,z363,z5,z6]),(0,[z7,z2,z3,z4,z5,z987]),(0,[z7,z2,z3,z4,z988,z6]),(0,[z1,z2,z3,z4,z73,z34]),(0,[z7,z2,z3,z189,z17,z6]),(0,[z7,z2,z3,z4,z989,z6]),(0,[z7,z115,z3,z4,z27,z6]),(1,[z7,z2,z832,z5,z6]),(0,[z7,z2,z3,z4,z5,z180])],[(0,[z52,z2,z3,z4,z5,z168]),(0,[z7,z2,z3,z990,z5,z6]),(0,[z7,z2,z4,z5,z991,z6]),(0,[z7,z2,z3,z4,z5,z992]),(0,[z993,z2,z3,z4,z5,z6]),(0,[z7,z2,z237,z3,z5,z762])],[(0,[z9,z2,z3,z509,z5,z6]),(1,[z2,z3,z4,z5,z849]),(0,[z7,z2,z3,z4,z5,z994]),(0,[z2,z3,z995,z4,z5,z6]),(0,[z2,z3,z4,z526,z59,z6]),(0,[z7,z2,z3,z4,z5,z880])],[(0,[z41,z2,z97,z4,z5,z6]),(0,[z40,z7,z915,z4,z5,z6]),(0,[z7,z2,z3,z4,z27,z921]),(0,[z95,z2,z3,z4,z27,z6]),(0,[z44,z2,z3,z4,z27,z6]),(0,[z125,z7,z3,z4,z117,z80]),(0,[z996,z2,z3,z4,z5,z6]),(0,[z7,z2,z437,z4,z5,z19])],[(0,[z562,z2,z120,z4,z5,z6]),(0,[z997,z2,z3,z4,z5,z6]),(0,[z7,z2,z998,z3,z4,z6]),(0,[z7,z157,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z27,z923]),(0,[z7,z26,z2,z66,z48,z6])],[(0,[z7,z2,z3,z4,z999,z6]),(0,[z52,z65,z3,z4,z488,z6]),(0,[z7,z2,z3,z4,z8,z6]),(0,[z75,z2,z3,z4,z188,z6]),(0,[z7,z2,z3,z4,z12,z429])]],
   [[(0,[z2,z3,z4,z357,z13,z6]),(0,[z7,z2,z3,z4,z73,z34]),(0,[z1000,z2,z3,z4,z5,z6]),(0,[z7,z2,z452,z3,z4,z27]),(0,[z2,z1001,z3,z4,z17,z6])],[(0,[z7,z2,z3,z105,z4,z211]),(0,[z7,z2,z3,z4,z1002,z304]),(0,[z7,z2,z36,z3,z295,z6])],[(0,[z1,z2,z3,z4,z488,z6]),(0,[z7,z2,z3,z4,z5,z1003]),(0,[z7,z2,z3,z189,z27,z6]),(0,[z7,z345,z3,z47,z5,z6]),(0,[z2,z1004,z3,z4,z5,z6])],[(0,[z7,z2,z90,z4,z5,z6]),(0,[z65,z3,z232,z4,z5,z6]),(0,[z7,z2,z1005,z4,z5,z6]),(0,[z41,z2,z3,z4,z313,z6]),(0,[z40,z7,z61,z4,z313,z6]),(0,[z7,z2,z3,z4,z1006,z6])],[(0,[z7,z2,z3,z4,z5,z1007]),(0,[z1008,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z12,z511])],[(0,[z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z1009,z6]),(0,[z0,z2,z3,z4,z5,z849]),(0,[z7,z2,z1010,z3,z4,z5]),(0,[z671,z7,z3,z109,z5,z6]),(0,[z1011,z7,z2,z4,z27,z6]),(0,[z7,z2,z452,z3,z4,z5]),(0,[z7,z2,z364,z303,z5,z6])],[(0,[z7,z2,z3,z1012,z5,z6]),(0,[z7,z2,z3,z4,z5,z1013]),(0,[z0,z2,z3,z4,z5,z546]),(0,[z7,z2,z3,z4,z99,z38]),(0,[z978,z2,z3,z4,z15,z6]),(0,[z7,z306,z2,z48,z5,z6]),(0,[z7,z940,z2,z4,z27,z6]),(0,[z7,z2,z18,z4,z17,z19]),(0,[z7,z1014,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z399])],[(0,[z7,z2,z151,z4,z184,z6]),(0,[z52,z667,z3,z4,z5,z6]),(0,[z945,z2,z3,z4,z5,z6]),(0,[z7,z2,z870,z3,z4,z5]),(0,[z7,z2,z3,z693,z5,z21])]],
   [[(0,[z113,z2,z3,z4,z5,z242]),(0,[z236,z2,z3,z4,z55,z6]),(0,[z54,z7,z3,z109,z79,z6]),(0,[z1015,z2,z3,z4,z5,z6]),(0,[z7,z3,z4,z67,z17,z6]),(0,[z35,z2,z126,z4,z5,z6]),(0,[z7,z2,z3,z4,z1016,z6])],[(0,[z7,z2,z3,z4,z1017,z6]),(0,[z7,z2,z3,z4,z17,z429]),(0,[z2,z3,z4,z5,z141,z1018]),(0,[z7,z2,z37,z4,z147,z141])],[(0,[z2,z3,z4,z17,z243,z6]),(0,[z7,z2,z3,z4,z5,z933]),(0,[z2,z3,z4,z5,z243,z80])],[(0,[z0,z2,z3,z4,z5,z34]),(0,[z7,z2,z364,z4,z5,z6]),(0,[z70,z2,z3,z4,z5,z275]),(0,[z7,z2,z3,z4,z17,z1019]),(0,[z7,z2,z3,z4,z1020,z6])],[(0,[z7,z2,z3,z4,z184,z168]),(0,[z52,z65,z3,z4,z466,z6]),(0,[z7,z2,z3,z1021,z5,z6]),(0,[z41,z2,z3,z4,z5,z369]),(0,[z40,z7,z61,z4,z5,z369]),(0,[z7,z2,z3,z148,z27,z21]),(0,[z2,z3,z4,z17,z1022,z6]),(0,[z7,z2,z3,z783,z295,z6]),(0,[z7,z2,z3,z4,z340,z6]),(0,[z7,z1023,z2,z4,z5,z6])],[(0,[z7,z2,z1024,z4,z5,z6]),(0,[z7,z2,z452,z3,z4,z12]),(0,[z125,z7,z3,z4,z116,z80]),(0,[z7,z2,z3,z225,z5,z21])],[(1,[z2,z749,z4,z5,z6]),(0,[z7,z2,z3,z4,z145,z242]),(0,[z7,z2,z126,z4,z5,z39]),(0,[z111,z7,z2,z3,z4,z399])],[(0,[z7,z2,z3,z4,z1025,z6]),(0,[z946,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z1026,z3,z4,z5]),(0,[z223,z2,z3,z4,z17,z83]),(0,[z7,z2,z140,z4,z17,z6]),(0,[z7,z30,z3,z4,z27,z6])],[(0,[z2,z3,z4,z12,z13,z83]),(0,[z7,z2,z3,z4,z27,z429])],[(0,[z2,z90,z69,z4,z5,z6]),(0,[z490,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z211,z13]),(0,[z7,z2,z3,z4,z313,z6]),(0,[z7,z2,z126,z303,z5,z6]),(0,[z7,z2,z3,z4,z1027,z6]),(0,[z7,z2,z3,z4,z340,z12])],[(0,[z7,z2,z3,z4,z5,z1028]),(0,[z164,z2,z3,z4,z5,z83]),(0,[z163,z2,z3,z4,z5,z38]),(0,[z7,z2,z3,z4,z1029,z6]),(0,[z7,z2,z3,z4,z1030,z6]),(0,[z2,z3,z4,z190,z27,z6]),(0,[z1031,z2,z3,z4,z5,z6]),(0,[z1032,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z17,z168]),(0,[z2,z280,z3,z4,z5,z6]),(0,[z41,z2,z3,z92,z5,z6]),(0,[z113,z2,z3,z4,z313,z6]),(0,[z40,z7,z61,z92,z5,z6]),(0,[z7,z2,z3,z4,z1033,z6])],[(0,[z7,z2,z3,z4,z1034,z6]),(0,[z7,z2,z3,z4,z1035,z6]),(0,[z7,z2,z3,z4,z1036,z6]),(0,[z7,z2,z3,z4,z103,z6]),(0,[z125,z7,z3,z4,z17,z80])],[(0,[z2,z3,z4,z5,z567,z83]),(0,[z7,z2,z3,z4,z1037,z6]),(0,[z7,z115,z452,z3,z4,z27]),(0,[z7,z2,z3,z4,z17,z880])],[(0,[z0,z2,z3,z4,z5,z623]),(0,[z7,z2,z3,z4,z1038,z6]),(0,[z7,z2,z3,z4,z15,z6]),(0,[z7,z2,z179,z4,z5,z6]),(0,[z7,z2,z3,z4,z1039,z6]),(0,[z111,z7,z2,z4,z343,z6]),(0,[z7,z2,z3,z503,z5,z21])]],
   [[(0,[z7,z2,z3,z363,z5,z6]),(0,[z223,z2,z3,z4,z27,z83]),(0,[z54,z70,z3,z109,z5,z6]),(0,[z7,z2,z3,z4,z55,z275]),(0,[z2,z967,z3,z4,z5,z6]),(0,[z2,z3,z4,z375,z721,z6]),(0,[z7,z2,z3,z4,z12,z560])],[(0,[z2,z3,z4,z5,z13,z168]),(0,[z70,z2,z3,z4,z5,z6]),(0,[z7,z2,z1026,z3,z4,z466]),(0,[z7,z462,z3,z4,z27,z6]),(0,[z7,z2,z3,z832,z5,z6]),(0,[z7,z2,z18,z4,z5,z715])],[(0,[z7,z2,z3,z4,z1040,z6]),(0,[z40,z562,z61,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1041]),(0,[z7,z599,z3,z4,z27,z6]),(0,[z7,z2,z3,z4,z27,z984]),(0,[z2,z3,z4,z27,z243,z6]),(0,[z7,z2,z126,z4,z117,z6]),(0,[z111,z7,z2,z4,z789,z6]),(0,[z7,z2,z3,z4,z1042,z6])],[(0,[z7,z2,z3,z4,z5,z1043]),(0,[z1044,z2,z3,z4,z5,z6]),(0,[z70,z2,z3,z4,z5,z130]),(0,[z236,z2,z140,z4,z5,z6]),(0,[z7,z2,z3,z4,z211,z188]),(0,[z1045,z2,z3,z4,z27,z6]),(0,[z7,z2,z1046,z3,z4,z27])],[(0,[z210,z2,z46,z4,z5,z6]),(0,[z7,z2,z3,z4,z1047,z6]),(0,[z164,z2,z3,z4,z73,z6]),(0,[z1048,z2,z3,z4,z5,z6]),(0,[z7,z159,z3,z4,z17,z6])],[(0,[z2,z90,z4,z5,z13,z6]),(0,[z7,z2,z3,z4,z1049,z6]),(0,[z1,z2,z3,z4,z707,z6]),(0,[z113,z2,z3,z4,z5,z369]),(0,[z7,z2,z3,z4,z375,z6]),(0,[z125,z7,z3,z4,z27,z80]),(0,[z7,z2,z364,z4,z116,z6]),(0,[z7,z2,z3,z4,z12,z103]),(0,[z7,z2,z3,z4,z1050,z6])],[(0,[z7,z2,z3,z1051,z5,z6]),(0,[z7,z2,z3,z4,z5,z1052]),(0,[z7,z2,z3,z4,z5,z1053]),(0,[z1054,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1055]),(0,[z2,z63,z3,z4,z5,z168]),(0,[z7,z2,z3,z1056,z5,z6]),(0,[z7,z2,z3,z4,z5,z1057]),(0,[z1058,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z253,z46,z4,z5,z6]),(0,[z7,z2,z3,z4,z17,z242]),(0,[z7,z2,z1046,z3,z4,z5]),(0,[z16,z3,z4,z17,z27,z6]),(0,[z7,z157,z3,z4,z773,z6]),(0,[z7,z199,z3,z4,z5,z39]),(0,[z7,z2,z3,z303,z5,z80]),(0,[z7,z2,z3,z4,z1059,z6])],[(0,[z7,z2,z1060,z3,z4,z5]),(0,[z7,z2,z3,z4,z1061,z6]),(0,[z7,z2,z452,z3,z4,z78])],[(0,[z7,z2,z3,z4,z1062,z6]),(0,[z1063,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z388,z5,z6]),(0,[z94,z2,z77,z3,z4,z5])],[(0,[z7,z2,z3,z4,z5,z1064]),(0,[z7,z2,z3,z4,z1065,z5]),(0,[z2,z120,z749,z4,z5,z6]),(0,[z7,z2,z3,z4,z707,z6]),(0,[z7,z2,z3,z189,z5,z6]),(0,[z7,z2,z3,z4,z145,z369]),(0,[z2,z3,z1066,z4,z5,z6]),(0,[z7,z2,z3,z4,z1067,z6])],[(0,[z7,z96,z97,z4,z5,z6]),(0,[z1068,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z1069,z6])],[(0,[z7,z2,z3,z1070,z5,z6]),(0,[z7,z2,z3,z4,z1071,z6]),(0,[z7,z2,z3,z4,z1072,z6]),(0,[z113,z2,z3,z92,z5,z6]),(0,[z113,z2,z3,z189,z5,z6]),(0,[z7,z2,z3,z4,z1073,z6]),(0,[z2,z255,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z795,z5]),(0,[z7,z2,z297,z4,z5,z19])],[(0,[z1011,z7,z2,z4,z5,z6]),(0,[z7,z2,z3,z4,z55,z6]),(0,[z2,z3,z118,z47,z5,z6]),(0,[z7,z175,z3,z4,z17,z6]),(0,[z7,z2,z126,z4,z12,z5]),(0,[z1074,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z1075,z6])],[(0,[z23,z2,z527,z4,z5,z6]),(0,[z7,z2,z3,z4,z1076,z6]),(0,[z7,z2,z1077,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1078]),(1,[z7,z2,z3,z5,z762])]],
   [[(0,[z1079,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z27,z242]),(0,[z7,z2,z3,z4,z55,z130]),(0,[z7,z2,z3,z1012,z27,z6]),(0,[z7,z2,z3,z4,z27,z399]),(0,[z7,z2,z102,z3,z410,z6]),(0,[z7,z2,z364,z388,z5,z6]),(0,[z2,z1080,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z1081,z6]),(0,[z7,z2,z3,z4,z1082,z6]),(0,[z111,z7,z2,z4,z598,z6]),(0,[z2,z1001,z3,z4,z5,z6]),(0,[z1083,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z73,z221]),(0,[z7,z2,z3,z146,z206,z6]),(0,[z7,z2,z126,z4,z116,z6]),(0,[z7,z2,z3,z4,z1084,z6])],[(0,[z32,z2,z46,z4,z5,z6]),(0,[z7,z2,z3,z4,z1085,z6]),(0,[z7,z2,z1086,z4,z5,z6]),(0,[z2,z3,z4,z144,z5,z83]),(0,[z70,z2,z179,z4,z5,z6]),(0,[z7,z2,z140,z4,z5,z275]),(0,[z2,z3,z4,z5,z1087,z6]),(0,[z7,z2,z3,z4,z936,z6])],[(0,[z7,z2,z3,z4,z1065,z466]),(0,[z7,z2,z3,z4,z99,z83]),(0,[z7,z2,z3,z4,z5,z1088]),(0,[z7,z2,z4,z27,z991,z6]),(0,[z7,z2,z3,z4,z211,z17]),(0,[z490,z2,z3,z4,z17,z6]),(0,[z1089,z2,z3,z4,z5,z6])],[(0,[z150,z241,z3,z4,z5,z6]),(0,[z460,z2,z46,z4,z5,z6]),(0,[z7,z2,z1090,z4,z5,z6]),(0,[z1091,z2,z3,z4,z5,z6]),(0,[z7,z2,z364,z4,z27,z6]),(0,[z2,z255,z3,z4,z27,z6]),(0,[z2,z3,z4,z5,z87,z39])],[(0,[z9,z2,z3,z681,z5,z6]),(0,[z7,z2,z3,z4,z1092,z6]),(0,[z436,z2,z3,z4,z17,z6]),(0,[z2,z127,z255,z28,z5,z6]),(0,[z7,z2,z3,z4,z1093,z6]),(0,[z7,z2,z3,z4,z1094,z6])],[(0,[z7,z2,z3,z4,z5,z1095]),(0,[z7,z2,z3,z4,z1096,z6]),(0,[z94,z2,z3,z4,z5,z39]),(0,[z7,z2,z18,z4,z5,z19])]],
   [[(0,[z7,z2,z3,z1097,z5,z6]),(0,[z7,z2,z151,z296,z5,z6]),(0,[z7,z2,z1098,z4,z5,z6]),(0,[z7,z2,z1099,z4,z5,z6]),(0,[z7,z2,z3,z189,z313,z6]),(0,[z7,z199,z3,z4,z103,z39]),(0,[z7,z2,z3,z4,z432,z19])],[(0,[z7,z2,z3,z4,z5,z1100]),(0,[z7,z2,z3,z4,z1101,z6]),(0,[z7,z2,z359,z4,z58,z6]),(0,[z1102,z2,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z1103,z6]),(0,[z7,z2,z3,z4,z1104,z6]),(0,[z7,z2,z1105,z4,z5,z6]),(0,[z7,z2,z3,z148,z432,z21])],[(0,[z7,z2,z1106,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z1107]),(0,[z7,z2,z126,z4,z17,z6]),(0,[z7,z2,z37,z4,z605,z6]),(0,[z7,z2,z3,z105,z167,z6]),(0,[z7,z2,z3,z4,z5,z429])],[(0,[z40,z84,z61,z4,z5,z6]),(0,[z7,z499,z2,z48,z5,z6]),(0,[z7,z2,z37,z4,z58,z6]),(0,[z2,z3,z1108,z4,z5,z6]),(0,[z1109,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z105,z167,z399]),(0,[z2,z3,z4,z1110,z5,z6])],[(0,[z150,z253,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z1111,z6]),(0,[z7,z611,z2,z48,z5,z6]),(0,[z490,z2,z3,z4,z27,z6]),(0,[z7,z2,z3,z4,z5,z1019]),(0,[z7,z2,z3,z388,z116,z6])],[(0,[z7,z2,z3,z296,z5,z168]),(0,[z32,z2,z662,z4,z5,z6]),(0,[z7,z2,z3,z4,z17,z369]),(0,[z7,z2,z3,z4,z1112,z6]),(0,[z7,z2,z592,z4,z5,z19]),(0,[z318,z2,z3,z4,z17,z6])],[(0,[z7,z3,z4,z660,z27,z6]),(0,[z7,z2,z1113,z4,z5,z6]),(0,[z2,z3,z118,z109,z5,z6]),(0,[z1114,z2,z3,z4,z5,z6]),(0,[z436,z2,z3,z4,z27,z6]),(0,[z2,z280,z3,z4,z27,z6]),(0,[z7,z2,z3,z4,z432,z71]),(0,[z7,z2,z3,z5,z20,z762])],[(0,[z7,z2,z1115,z3,z4,z6]),(0,[z7,z2,z3,z4,z1116,z6]),(0,[z7,z2,z3,z5,z1117,z6]),(0,[z2,z3,z4,z27,z1118,z6]),(0,[z861,z2,z3,z4,z5,z86]),(0,[z7,z2,z3,z4,z1119,z6])]],
   [[(0,[z7,z2,z151,z4,z5,z6]),(0,[z335,z2,z3,z4,z5,z83]),(0,[z7,z2,z179,z4,z55,z6]),(0,[z7,z2,z3,z4,z211,z643]),(0,[z7,z2,z77,z126,z4,z5]),(0,[z7,z199,z3,z4,z375,z39]),(0,[z7,z26,z2,z48,z5,z86])],[(0,[z2,z3,z786,z10,z5,z6]),(0,[z223,z2,z3,z4,z5,z83]),(0,[z7,z2,z140,z4,z5,z6]),(0,[z2,z3,z4,z1022,z5,z6]),(0,[z7,z2,z3,z47,z5,z275]),(0,[z2,z3,z4,z74,z917,z6]),(0,[z966,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z1120,z5,z6]),(0,[z7,z2,z3,z4,z340,z429])],[(0,[z7,z2,z3,z4,z184,z216]),(0,[z7,z2,z3,z1121,z5,z6]),(0,[z7,z2,z3,z4,z5,z1122]),(0,[z70,z2,z3,z4,z55,z6]),(0,[z7,z2,z126,z4,z27,z6]),(0,[z1123,z2,z3,z4,z17,z6]),(0,[z7,z2,z3,z524,z167,z6])],[(0,[z7,z2,z90,z4,z5,z168]),(0,[z7,z2,z3,z4,z1124,z6]),(0,[z7,z2,z3,z1125,z5,z6]),(0,[z7,z2,z140,z4,z5,z130]),(0,[z7,z2,z1126,z4,z5,z6]),(0,[z94,z2,z3,z4,z117,z6])],[(0,[z7,z2,z3,z4,z1127,z6]),(0,[z7,z408,z3,z4,z27,z6]),(0,[z1045,z2,z3,z4,z5,z6]),(0,[z1063,z2,z3,z4,z17,z6]),(0,[z111,z95,z2,z4,z343,z6]),(0,[z7,z2,z3,z4,z5,z1128])],[(0,[z7,z2,z3,z4,z5,z168]),(0,[z7,z272,z3,z4,z17,z6]),(0,[z7,z2,z3,z92,z17,z6]),(0,[z7,z2,z3,z4,z27,z369]),(0,[z7,z250,z3,z4,z27,z6]),(0,[z7,z2,z3,z4,z1129,z6])],[(0,[z125,z7,z3,z4,z5,z80])],[(0,[z7,z2,z3,z4,z5,z1130]),(0,[z7,z2,z3,z4,z231,z216]),(0,[z7,z2,z3,z4,z5,z1131]),(0,[z7,z2,z3,z4,z78,z180]),(1,[z7,z2,z3,z783,z6])]],
   [[],[(0,[z7,z2,z3,z1132,z5,z6]),(0,[z7,z2,z3,z4,z1133,z6]),(0,[z7,z2,z1134,z4,z5,z6]),(0,[z1135,z2,z3,z4,z5,z6]),(0,[z1136,z2,z3,z4,z5,z6])],[(0,[z32,z2,z700,z4,z5,z6]),(0,[z7,z2,z3,z4,z1137,z6]),(0,[z7,z199,z3,z4,z27,z39]),(0,[z7,z2,z110,z3,z4,z211]),(0,[z2,z3,z4,z238,z59,z6]),(0,[z7,z2,z3,z4,z5,z1138])],[(0,[z7,z2,z3,z4,z1139,z6]),(0,[z7,z2,z3,z4,z1140,z6]),(0,[z150,z63,z151,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1141]),(0,[z1142,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1143])],[(0,[z461,z2,z46,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1144]),(0,[z7,z2,z3,z388,z27,z6]),(0,[z7,z3,z4,z17,z773,z6]),(0,[z125,z7,z364,z4,z5,z80]),(0,[z1145,z2,z3,z4,z5,z6])],[(0,[z32,z2,z46,z4,z17,z6]),(0,[z7,z2,z3,z4,z1146,z6]),(0,[z7,z2,z3,z92,z27,z6]),(0,[z2,z255,z61,z4,z5,z6]),(0,[z125,z94,z3,z4,z5,z80]),(0,[z2,z127,z28,z118,z5,z6]),(0,[z2,z3,z4,z5,z1018,z6]),(0,[z1147,z2,z3,z4,z5,z6])],[(0,[z7,z2,z915,z4,z5,z6]),(0,[z1068,z2,z3,z4,z27,z6]),(0,[z122,z7,z2,z4,z451,z6]),(0,[z2,z1148,z3,z4,z5,z6])],[(0,[z7,z2,z3,z1149,z5,z6]),(0,[z7,z2,z3,z1150,z5,z6]),(0,[z7,z2,z3,z4,z5,z1151]),(0,[z2,z1152,z3,z4,z5,z6])]],
   [[(0,[z150,z63,z3,z4,z5,z168]),(0,[z7,z2,z3,z4,z5,z1153]),(0,[z2,z3,z4,z786,z5,z6]),(0,[z2,z3,z4,z17,z59,z6]),(0,[z2,z3,z1154,z4,z5,z6]),(0,[z7,z2,z36,z3,z76,z6]),(0,[z7,z2,z3,z167,z783,z6])],[(0,[z16,z2,z3,z4,z231,z6]),(0,[z7,z2,z3,z4,z1155,z6]),(0,[z7,z2,z3,z4,z1156,z6]),(0,[z16,z2,z3,z4,z73,z6]),(0,[z7,z2,z3,z4,z5,z242]),(0,[z7,z2,z3,z109,z5,z275]),(0,[z2,z3,z4,z5,z1118,z6])],[(0,[z7,z659,z97,z4,z5,z6]),(0,[z7,z2,z1157,z4,z5,z6]),(0,[z7,z2,z1158,z4,z5,z6]),(0,[z7,z2,z3,z4,z1002,z6])],[(0,[z7,z2,z3,z4,z488,z6]),(0,[z7,z2,z151,z363,z5,z6]),(0,[z7,z2,z3,z296,z231,z6]),(0,[z2,z366,z46,z4,z5,z6]),(0,[z7,z2,z3,z4,z1159,z6]),(0,[z7,z1160,z2,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1161])],[(0,[z7,z2,z1162,z4,z5,z6]),(0,[z1163,z2,z3,z4,z5,z6]),(0,[z2,z66,z1004,z3,z4,z6]),(0,[z1164,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z432,z6])],[(0,[z1,z2,z3,z4,z231,z6]),(0,[z32,z2,z46,z4,z27,z6]),(0,[z1,z2,z3,z4,z73,z6]),(0,[z1165,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z1166,z6]),(0,[z2,z3,z4,z1167,z5,z6]),(0,[z70,z2,z140,z4,z5,z6]),(0,[z7,z2,z1168,z4,z5,z6]),(0,[z2,z77,z3,z4,z5,z87])],[(0,[z2,z3,z1169,z4,z5,z6]),(0,[z2,z255,z3,z4,z5,z6]),(0,[z7,z2,z3,z1170,z5,z6]),(0,[z7,z2,z3,z1171,z5,z6]),(0,[z7,z14,z97,z4,z194,z6]),(0,[z7,z2,z3,z4,z5,z1172]),(0,[z7,z2,z1173,z4,z5,z6]),(0,[z7,z258,z3,z4,z27,z6])],[(0,[z7,z2,z3,z4,z1174,z6]),(0,[z7,z2,z162,z28,z5,z6]),(0,[z7,z2,z452,z3,z4,z17])]],
   [[(0,[z7,z2,z3,z363,z5,z168]),(0,[z7,z2,z3,z1175,z5,z6]),(0,[z7,z2,z3,z4,z739,z529]),(0,[z7,z2,z1176,z4,z5,z6]),(0,[z7,z2,z110,z3,z295,z6])],[(0,[z2,z3,z69,z4,z5,z168]),(0,[z7,z2,z18,z4,z27,z19]),(0,[z7,z2,z3,z4,z5,z762])],[(0,[z7,z2,z151,z4,z17,z6]),(0,[z7,z2,z3,z4,z5,z1177]),(0,[z1,z2,z3,z4,z635,z6]),(0,[z7,z2,z3,z4,z5,z1178]),(0,[z7,z2,z452,z3,z4,z103])],[(0,[z7,z2,z3,z4,z1179,z6]),(0,[z7,z2,z3,z4,z1180,z6]),(0,[z54,z7,z3,z109,z5,z130]),(0,[z7,z2,z3,z4,z1181,z6])],[(0,[z7,z2,z1106,z3,z27,z6]),(0,[z7,z3,z297,z4,z27,z6])],[(0,[z7,z2,z3,z4,z1182,z6]),(0,[z7,z2,z3,z4,z1183,z6]),(0,[z7,z2,z61,z4,z5,z369]),(0,[z7,z2,z3,z4,z1184,z6]),(0,[z2,z3,z4,z12,z59,z6]),(0,[z7,z2,z28,z832,z5,z6]),(0,[z1185,z2,z3,z4,z5,z6])],[(0,[z7,z2,z1186,z4,z5,z6]),(0,[z7,z2,z3,z1187,z5,z6]),(0,[z7,z2,z3,z4,z1188,z6]),(0,[z7,z2,z3,z4,z313,z242]),(0,[z2,z3,z4,z1189,z5,z6]),(0,[z7,z2,z37,z4,z147,z180])],[(0,[z32,z2,z90,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1190]),(0,[z436,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z1191,z5,z6]),(0,[z7,z26,z2,z48,z17,z6])]],
   [[(0,[z7,z2,z3,z4,z466,z6]),(0,[z562,z2,z90,z4,z5,z6]),(0,[z2,z3,z69,z215,z5,z6]),(0,[z223,z2,z3,z4,z5,z849]),(0,[z1114,z2,z3,z4,z27,z6]),(0,[z7,z2,z131,z4,z147,z6]),(0,[z7,z2,z3,z4,z5,z1192])],[(0,[z7,z2,z3,z4,z5,z1193]),(0,[z2,z3,z69,z5,z218,z6]),(1,[z7,z915,z4,z5,z6]),(0,[z7,z2,z3,z4,z1194,z6]),(0,[z7,z2,z179,z47,z5,z6]),(0,[z7,z2,z77,z3,z4,z116]),(0,[z111,z318,z2,z4,z343,z6]),(0,[z7,z2,z3,z1195,z5,z6]),(0,[z7,z2,z3,z4,z5,z1196])],[(0,[z562,z2,z3,z4,z5,z6]),(0,[z7,z2,z151,z4,z27,z6]),(0,[z7,z2,z3,z4,z1197,z6]),(0,[z54,z236,z3,z109,z5,z6]),(0,[z1102,z2,z3,z4,z5,z6]),(0,[z360,z2,z3,z4,z643,z6]),(0,[z7,z2,z3,z1198,z5,z6])],[(0,[z7,z2,z3,z1199,z5,z6]),(0,[z2,z3,z4,z1200,z5,z6]),(0,[z7,z2,z3,z4,z1201,z6]),(0,[z7,z2,z126,z4,z5,z6]),(0,[z7,z14,z97,z4,z27,z6]),(0,[z70,z2,z3,z47,z5,z6]),(0,[z236,z2,z3,z4,z79,z6]),(0,[z7,z2,z140,z4,z27,z6]),(0,[z7,z365,z3,z4,z17,z6]),(0,[z7,z2,z77,z3,z303,z5]),(0,[z125,z7,z3,z388,z5,z80]),(0,[z2,z3,z4,z132,z1202,z6])],[(0,[z457,z7,z61,z4,z5,z6]),(0,[z7,z2,z3,z4,z78,z805])],[(0,[z7,z2,z3,z4,z5,z1203]),(0,[z7,z2,z61,z92,z5,z6]),(0,[z7,z2,z3,z4,z1204,z6])],[(0,[z150,z63,z3,z4,z231,z6]),(0,[z2,z3,z1205,z4,z5,z6]),(0,[z318,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z1206,z6]),(0,[z7,z2,z3,z4,z5,z369]),(0,[z1207,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z27,z168]),(0,[z7,z2,z3,z1208,z5,z6]),(0,[z7,z2,z3,z4,z5,z1209]),(0,[z7,z2,z3,z4,z1210,z6]),(0,[z7,z2,z237,z3,z17,z20]),(0,[z1211,z2,z3,z4,z5,z6]),(0,[z7,z26,z2,z832,z5,z6]),(0,[z7,z2,z1212,z3,z4,z6]),(0,[z7,z2,z3,z105,z167,z429]),(0,[z2,z237,z3,z5,z20,z87])]],
   [[(0,[z7,z2,z3,z1213,z5,z6]),(0,[z7,z161,z3,z47,z17,z6]),(0,[z7,z2,z3,z4,z1214,z6]),(0,[z2,z1215,z3,z4,z5,z6])],[(0,[z7,z2,z1216,z4,z5,z6]),(0,[z2,z3,z4,z5,z1217,z6]),(0,[z122,z7,z2,z3,z4,z211]),(0,[z7,z2,z77,z3,z4,z211]),(0,[z2,z3,z4,z716,z17,z6]),(0,[z7,z2,z37,z4,z147,z6])],[(0,[z7,z2,z3,z4,z5,z1218]),(0,[z7,z2,z3,z4,z12,z56])],[(0,[z7,z2,z3,z296,z5,z216]),(0,[z98,z2,z3,z10,z17,z6]),(0,[z7,z2,z3,z4,z1219,z6]),(0,[z1123,z2,z3,z4,z5,z6]),(0,[z1135,z2,z3,z4,z27,z6]),(0,[z7,z2,z262,z3,z4,z238]),(0,[z95,z2,z3,z4,z78,z6]),(0,[z7,z2,z3,z1220,z5,z6])],[(0,[z2,z3,z4,z231,z13,z6]),(0,[z7,z2,z1221,z4,z5,z6]),(0,[z7,z2,z3,z4,z220,z180]),(0,[z119,z2,z237,z3,z5,z20])],[(0,[z552,z2,z3,z4,z13,z6]),(0,[z7,z2,z3,z4,z27,z1141]),(0,[z7,z2,z3,z4,z1222,z6]),(0,[z2,z3,z4,z12,z5,z243])],[(0,[z7,z2,z3,z363,z231,z6]),(1,[z2,z3,z786,z5,z6]),(0,[z152,z2,z3,z4,z13,z6]),(0,[z7,z2,z3,z92,z5,z6]),(0,[z1223,z2,z3,z4,z5,z6]),(0,[z7,z2,z77,z3,z4,z238])],[(0,[z0,z2,z3,z4,z5,z447]),(0,[z7,z2,z3,z189,z5,z242]),(0,[z7,z2,z3,z4,z1224,z6]),(0,[z2,z1225,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z1226,z6]),(0,[z7,z2,z237,z3,z27,z20]),(0,[z7,z2,z3,z4,z1227,z6])]],
   [[(0,[z7,z2,z3,z4,z1228,z6]),(0,[z7,z2,z3,z27,z1117,z6]),(0,[z7,z26,z2,z382,z48,z6]),(0,[z7,z2,z3,z4,z1229,z6]),(0,[z790,z2,z3,z4,z132,z6])],[(0,[z7,z2,z3,z4,z5,z849]),(0,[z7,z2,z179,z109,z5,z6]),(0,[z35,z2,z3,z303,z5,z6]),(0,[z7,z2,z3,z4,z783,z6])],[(0,[z7,z2,z1060,z3,z4,z194]),(0,[z743,z2,z3,z4,z17,z6]),(0,[z7,z2,z131,z4,z136,z6])],[(0,[z98,z2,z3,z10,z27,z6]),(0,[z7,z2,z3,z4,z1230,z6]),(0,[z7,z2,z3,z4,z1231,z6]),(0,[z7,z2,z3,z4,z313,z369]),(0,[z70,z2,z3,z109,z5,z6]),(0,[z7,z2,z3,z4,z79,z275]),(0,[z7,z2,z3,z4,z5,z1232]),(0,[z7,z2,z3,z4,z1233,z6]),(0,[z54,z108,z3,z109,z5,z6]),(0,[z54,z7,z3,z109,z17,z6]),(0,[z7,z646,z3,z4,z27,z6]),(0,[z2,z3,z4,z727,z27,z6])],[(0,[z32,z2,z3,z363,z5,z6]),(0,[z1234,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z1235,z5,z6]),(0,[z7,z2,z3,z4,z1236,z6]),(0,[z2,z1237,z3,z4,z5,z6]),(0,[z7,z2,z4,z27,z1238,z6])],[(0,[z108,z2,z3,z10,z5,z6]),(0,[z9,z2,z3,z786,z5,z6]),(0,[z7,z3,z4,z17,z185,z6]),(0,[z164,z2,z3,z4,z99,z6]),(0,[z7,z2,z97,z92,z5,z6]),(0,[z7,z2,z3,z1239,z5,z6]),(0,[z7,z3,z4,z17,z27,z6]),(0,[z7,z2,z3,z4,z1240,z6])],[(0,[z481,z2,z3,z10,z5,z6]),(0,[z7,z2,z4,z1241,z5,z6]),(0,[z7,z178,z3,z4,z5,z39]),(0,[z1242,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z208,z17,z6])],[(0,[z7,z2,z1243,z4,z5,z6]),(0,[z7,z1244,z3,z4,z5,z6]),(0,[z562,z2,z46,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1245]),(0,[z7,z2,z3,z303,z5,z39]),(0,[z7,z2,z3,z4,z220,z6])]],
   [[(0,[z7,z2,z3,z4,z529,z6]),(0,[z1246,z2,z3,z4,z5,z6])],[(0,[z35,z2,z3,z4,z117,z6]),(0,[z2,z3,z4,z1202,z5,z6])],[(0,[z766,z2,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z526,z407]),(0,[z1247,z2,z3,z4,z5,z6]),(0,[z2,z3,z1248,z4,z5,z6])],[(0,[z7,z2,z4,z1249,z5,z6]),(0,[z7,z2,z3,z92,z313,z6]),(0,[z7,z14,z915,z4,z5,z6]),(0,[z54,z7,z3,z109,z27,z6]),(0,[z1250,z2,z3,z4,z5,z6])],[(0,[z23,z2,z120,z4,z17,z6]),(0,[z562,z2,z3,z4,z17,z6]),(0,[z3,z4,z17,z59,z27,z6]),(0,[z122,z7,z2,z4,z343,z6]),(0,[z7,z2,z36,z3,z410,z6]),(0,[z7,z2,z3,z4,z5,z1251])],[(0,[z349,z7,z3,z109,z5,z6]),(0,[z7,z2,z756,z3,z5,z6]),(0,[z7,z398,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z220,z12]),(0,[z7,z2,z3,z4,z805,z149])],[(0,[z7,z2,z1252,z4,z5,z6]),(0,[z150,z63,z3,z4,z5,z216]),(0,[z94,z2,z3,z303,z5,z6]),(0,[z7,z2,z3,z4,z5,z1253]),(0,[z7,z2,z66,z3,z4,z6])],[(0,[z2,z3,z4,z5,z849,z6]),(0,[z7,z2,z3,z4,z12,z153]),(0,[z735,z2,z3,z4,z5,z6]),(0,[z7,z2,z1254,z3,z4,z6]),(0,[z7,z2,z3,z4,z78,z429])]],
   [[(0,[z2,z361,z3,z4,z5,z83]),(0,[z41,z2,z3,z4,z145,z6]),(0,[z40,z7,z61,z4,z145,z6]),(0,[z7,z2,z3,z4,z74,z6]),(0,[z7,z2,z3,z4,z1255,z6]),(0,[z2,z3,z118,z4,z17,z6]),(0,[z7,z2,z126,z388,z5,z6]),(0,[z7,z2,z4,z789,z343,z6])],[(0,[z7,z2,z3,z4,z79,z6]),(0,[z7,z1256,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z87,z6]),(0,[z7,z3,z915,z4,z5,z6]),(0,[z7,z2,z1257,z3,z4,z6]),(0,[z259,z7,z3,z4,z5,z80]),(0,[z7,z2,z3,z4,z5,z86]),(0,[z7,z2,z3,z4,z5,z1258]),(0,[z7,z26,z2,z48,z5,z304])],[(0,[z7,z2,z749,z4,z5,z6]),(0,[z164,z2,z3,z4,z5,z34]),(0,[z7,z2,z3,z4,z1259,z6]),(0,[z7,z2,z3,z4,z79,z130]),(0,[z7,z2,z3,z4,z5,z747]),(0,[z7,z2,z3,z4,z1260,z6]),(0,[z7,z2,z3,z4,z805,z5])],[(0,[z94,z2,z3,z4,z5,z6]),(0,[z7,z416,z3,z4,z17,z6]),(0,[z7,z14,z97,z4,z5,z6]),(0,[z7,z2,z3,z189,z5,z369]),(0,[z562,z2,z3,z4,z27,z6]),(0,[z7,z3,z4,z773,z5,z6]),(0,[z7,z2,z126,z4,z5,z80]),(0,[z7,z2,z3,z4,z1261,z6])],[(0,[z7,z2,z3,z4,z5,z1262]),(0,[z1263,z2,z3,z4,z5,z6]),(0,[z1264,z2,z3,z4,z5,z6]),(0,[z1265,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z1266,z6]),(0,[z7,z2,z3,z4,z805,z6])],[(0,[z7,z2,z3,z1267,z5,z6]),(0,[z7,z2,z3,z4,z5,z1268]),(0,[z7,z2,z3,z4,z5,z1269]),(0,[z7,z2,z1270,z4,z5,z6]),(0,[z7,z2,z4,z5,z1238,z6]),(0,[z2,z3,z4,z27,z1166,z6]),(0,[z7,z2,z1271,z3,z4,z27]),(0,[z7,z2,z3,z4,z1272,z6]),(0,[z7,z2,z3,z4,z12,z116]),(0,[z7,z2,z3,z4,z1273,z6]),(0,[z7,z2,z3,z4,z1274,z6])],[(0,[z2,z3,z4,z488,z13,z6]),(0,[z373,z2,z3,z4,z13,z6]),(0,[z7,z412,z3,z4,z17,z6]),(0,[z1275,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z3,z4,z27,z196,z6]),(0,[z318,z2,z3,z4,z27,z6]),(0,[z7,z26,z2,z48,z5,z6]),(0,[z1276,z2,z3,z4,z5,z6])],[(0,[z23,z2,z401,z4,z5,z6]),(0,[z98,z2,z3,z786,z5,z6]),(0,[z7,z2,z1277,z4,z5,z6]),(0,[z7,z2,z3,z4,z1278,z6]),(0,[z1279,z2,z3,z4,z5,z6]),(0,[z7,z2,z37,z3,z4,z211]),(0,[z35,z2,z3,z4,z116,z6]),(0,[z1280,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z789,z6]),(0,[z750,z2,z3,z4,z5,z141]),(0,[z7,z2,z3,z4,z12,z193])],[(0,[z7,z2,z3,z4,z1281,z6]),(0,[z7,z2,z3,z4,z13,z34]),(0,[z7,z241,z3,z4,z27,z6]),(0,[z7,z2,z36,z3,z81,z6]),(0,[z7,z2,z3,z105,z263,z6]),(0,[z7,z2,z37,z4,z474,z6])],[(0,[z7,z2,z1282,z4,z5,z6]),(0,[z7,z2,z1271,z3,z4,z5]),(0,[z1283,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z770,z5,z6]),(0,[z7,z2,z3,z4,z805,z12])],[(0,[z7,z199,z3,z4,z5,z794]),(0,[z7,z1284,z3,z4,z5,z6]),(0,[z7,z2,z1285,z4,z5,z6])],[(0,[z7,z2,z3,z1286,z5,z6]),(0,[z7,z2,z3,z4,z17,z216]),(0,[z7,z2,z3,z4,z1287,z6]),(0,[z7,z2,z170,z4,z5,z19]),(0,[z811,z2,z3,z4,z17,z6]),(0,[z7,z2,z3,z4,z132,z6]),(0,[z2,z1288,z3,z4,z5,z6]),(0,[z2,z1289,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1290]),(0,[z1291,z2,z3,z4,z5,z6]),(0,[z7,z2,z1292,z4,z5,z6]),(0,[z54,z7,z3,z109,z5,z275]),(0,[z7,z2,z237,z3,z5,z233]),(0,[z7,z2,z3,z4,z1293,z6]),(0,[z7,z2,z3,z4,z1294,z6])],[(0,[z106,z63,z3,z4,z5,z6]),(0,[z52,z470,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z145,z6]),(0,[z1295,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z211,z727,z27])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 512) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 512).take 522) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1034).take 260) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1294)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [512, 522, 260] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 91).take 95).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 186).take 70).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [91, 95, 70] = true :=
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

end PEqualNP.Outside.L_meta_38797

theorem PEqualNP.Outside.L_meta_38797 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4272613544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4272613544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38797.solve