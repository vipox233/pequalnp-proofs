import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45938

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
  Nat.testBit (4276677312 * 2 ^ 32 + 4276660864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0xb002040941464ce1#64 ++ 0xc008d8558010d956#64 ++ 0xf00f1e3fc7fffefb#64 ++ 0xfc0cfc7f8018ffff#64 : BitVec 256),
   (0x54b00a42889a136a#64 ++ 0xc862171968c61665#64 ++ 0xfff01fc7f8fe3f7e#64 ++ 0xf8731f99f8e71e67#64 : BitVec 256),
   (0x69552004d22c838b#64 ++ 0x1301a2e0de05a383#64 ++ 0xffffe007ff3fc7af#64 ++ 0x5b83e3e1ff07e387#64 : BitVec 256),
   (0x026952900031230a#64 ++ 0x02d403aa0da802a8#64 ++ 0x03fffff8003ffbcb#64 ++ 0x87fc03fe0ff803f8#64 : BitVec 256),
   (0x038e9d2724000010#64 ++ 0x21bf6c00037b6c00#64 ++ 0x03ffffffffc003f3#64 ++ 0xe3fffc000ffffc00#64 : BitVec 256),
   (0x80000000000000f4#64 ++ 0x03fffdffb0000000#64 ++ 0xfc000000000003fc#64 ++ 0x03fffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [6, 5]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [12, 9]⟩, ⟨.and, [13, 4]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0x03fffff8003ffbcb 0x87fc03fe0ff803f8

def z1 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x03ffffffffc003f3 0xe3fffc000ffffc00

def z2 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xfff01fc7f8fe3f7e 0xf8731f99f8e71e67

def z3 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xffffe007ff3fc7af 0x5b83e3e1ff07e387

def z4 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc000000000003fc 0x03fffffff0000000

def z5 : W := mkw 0x80800802000000f4 0x03fffdffb0420400 0xfff01fc7f8c003fe 0xe3fffffff8e71c00

def z6 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0xf00f1e3fc7fffefb 0xfc0cfc7f8018ffff

def z7 : W := mkw 0x024910000020030a 0x029402a00d280280 0x03fffff8003fc3cb 0x83fc03e00ff80380

def z8 : W := mkw 0x0000000000000060 0x0062151920000000 0xfc0000000000037c 0x00731f99f0000000

def z9 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0x03ffe007ff3fc483 0x5b80e0600f07e387

def z10 : W := mkw 0x1000000000020000 0xc000000000001044 0x00001e07c0fe3c02 0xf800000000001e67

def z11 : W := mkw 0x54b00a42889a130a 0xc800020048c61665 0x03f01fc7f8fe3c02 0xf800000008e71e67

def z12 : W := mkw 0x80000000000000e0 0x0309f8f590000000 0xfc000000000003fc 0x038ffffff0000000

def z13 : W := mkw 0x6bdfbd27f62c839b 0x33bfeee0df7fef83 0xffffffffffffc7ff 0xfbffffe1ffffff87

def z14 : W := mkw 0x80000000000000e4 0x024091ffb0000000 0xfc0000000000000c 0x000003fff0000000

def z15 : W := mkw 0x038c992624000014 0x23f725aa336b2400 0x0ff0e1c038000104 0x03f303807fe70000

def z16 : W := mkw 0x838e9d27240000f4 0x23fffdffb37b6c00 0xffffffffffc003ff 0xe3fffffffffffc00

def z17 : W := mkw 0x0000000000000014 0x03f725aa30000000 0x0c00000000000104 0x03f3038070000000

def z18 : W := mkw 0x8000000000000094 0x039de8e690000000 0x0000000000000080 0x038ce06600000000

def z19 : W := mkw 0x226952904035238b 0x02d483ea8da883aa 0xf3ffffffc73fffeb 0xdffce3ff8ff8e3ff

def z20 : W := mkw 0x004100000020030a 0x020002a00c000280 0x03ffe000003fc38b 0x038003e00f000380

def z21 : W := mkw 0x0228529000112000 0x00d4010a01a80028 0x00001ff800003840 0x847c001e00f80078

def z22 : W := mkw 0x9002040901424c60 0xc008581500105854 0x000f1e3800fffadb 0xa40c1c7e00181ff8

def z23 : W := mkw 0x0000000000000000 0x02d401aa00000000 0x00000000000003c8 0x03fc03fe00000000

def z24 : W := mkw 0x82695290003123fe 0x03ffffffbda802a8 0xfffffff8003ffbff 0x87fffffffff803f8

def z25 : W := mkw 0x0000000000000000 0x0000000000000000 0x000f1e38003ffacb 0x840c007e001803f8

def z26 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xfffffe3fff3fffef 0xdf8fe3ffff1fe3ff

def z27 : W := mkw 0x0000000000000014 0x03f725aa30000000 0x0c000000000003cc 0x03ff03fe70000000

def z28 : W := mkw 0x0000000000000010 0x01bf6c0000000000 0x00000000000003f0 0x03fffc0000000000

def z29 : W := mkw 0x0000000000000080 0x0301a0e090000000 0xfc000000000003ac 0x0383e3e1f0000000

def z30 : W := mkw 0x2945200452248081 0x1301a0e09601a182 0x000fe0000701c081 0x0380e0600700e180

def z31 : W := mkw 0x401000008008038a 0x0301a2e0d8040201 0xfff00007f83e07ae 0x5b83e3e1f8070207

def z32 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0x03f0fff800003940 0x87fc039e0ff80078

def z33 : W := mkw 0xb002040941464cf5 0xc3fffdffb010d956 0xfc0f1e3fc7ffffff 0xfffffffff018ffff

def z34 : W := mkw 0xf957240dd36ecfff 0xd3fffffffe15fbd7 0xfffffe3fffffffff 0xffffffffff1fffff

def z35 : W := mkw 0x6b5fb525f62c839b 0x339deae0df3deb83 0xffffe03fff3fc7af 0x5b8fe3e1ff1fe387

def z36 : W := mkw 0x030e952524000010 0x219d680003396800 0x000fe03807000081 0x038ce0000718e000

def z37 : W := mkw 0xb000000841464cf5 0xc3fffdffb0009156 0xfc000000003ffffc 0x1ffffffff00003ff

def z38 : W := mkw 0xa9452004522480f5 0x13fffdffb601a182 0xfc0fe0000701c3fd 0x03fffffff700e180

def z39 : W := mkw 0x2945200452248081 0x1301a0e09601a182 0xfc0fe0000701c3ad 0x0383e3e1f700e180

def z40 : W := mkw 0x038c992624000010 0x21b72400036b2400 0x03f0e1c038000100 0x03f300000fe70000

def z41 : W := mkw 0x03efdfb72431231a 0x23ff6faa0ffb6ea8 0x03fffffffffffbfb 0xe7fffffe0ffffff8

def z42 : W := mkw 0x56f95ad288bb336a 0xcaf617bb6dee16ed 0xfffffffff8ffffff 0xffff1fffffff1fff

def z43 : W := mkw 0x69552004d22c830b 0x110122004e05a383 0x03ffe007ff3fc7a3 0x5b83e0000f07e387

def z44 : W := mkw 0x69552004d22c830b 0x100002004e05a383 0x03ffe007ff3fc403 0x580000000f07e387

def z45 : W := mkw 0x6b7d7294d23da30b 0x12d403aa4fada3ab 0x03ffffffff3fffcb 0xdffc03fe0fffe3ff

def z46 : W := mkw 0x14a00a4208921060 0xc862151920c21464 0xfc001fc000c03b7c 0xa0731f99f0e01c60

def z47 : W := mkw 0x326b569941776f0b 0xc2d403aa0db8dbfe 0x03ffffffc7ffffcb 0xfffc03fe0ff8ffff

def z48 : W := mkw 0x495520049228830a 0x130122a05e052281 0x0ff0e00038000104 0x038303807f070000

def z49 : W := mkw 0x6b7d7294d23da38b 0x13d5a3eadfada3ab 0xffffffffff3fffef 0xdfffe3ffffffe3ff

def z50 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc0f1e38003ffbff 0x87fffffff01803f8

def z51 : W := mkw 0x54300240889a136a 0xc840131968841265 0xfc000000003e3c0c 0x18000399f0000267

def z52 : W := mkw 0x0228529000112000 0x00d4010a01a80028 0x000f1ff8003ffacb 0x847c007e00f803f8

def z53 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xfff001c7f8c00534 0x78731f81f8e71c07

def z54 : W := mkw 0x16aa9f632c921070 0xe8fe5d1921fa5c64 0x00001ff800c03850 0xa07c1c1800f81c60

def z55 : W := mkw 0x57be9f67ac9a137a 0xe9ff7f196bff7e65 0xfffffffffffe3fff 0xfbffff99fffffe67

def z56 : W := mkw 0x03eddbb62431231a 0x23f727aa0feb26a8 0x03fffff8383ffbcb 0x87ff03fe0fff03f8

def z57 : W := mkw 0x0000000000000000 0x0000000000000000 0xfc0000000000032c 0x00030381f0000000

def z58 : W := mkw 0xa002040941444cf5 0x03fffdffb010c912 0xfc0f00380701c3fd 0x07fffffff018e198

def z59 : W := mkw 0x1002040901424c00 0xc000000000105854 0x00001e3800c03800 0xa400000000181c78

def z60 : W := mkw 0x0000000000000014 0x00f6050a20000000 0x0000000000000000 0x0070000000000000

def z61 : W := mkw 0xfb7f769dd37fefeb 0xd3ddfbffdfbdfbff 0xffffffffffffffff 0xffffffffffffffff

def z62 : W := mkw 0x81040004000000f4 0x03fffdffb2012000 0xffffe007ff0003ff 0x43ffffffff07e000

def z63 : W := mkw 0x1000000000020060 0xc000101100001044 0xf0001e07c0fe3e7a 0xf8001c1980001e67

def z64 : W := mkw 0xe9142004d20c80f5 0x13fffdfff205a103 0xfc000007ff0007fc 0x5bfffffff007e007

def z65 : W := mkw 0x0000000000000070 0x01ff7d1920000000 0xfc000000000003fc 0x03ffff99f0000000

def z66 : W := mkw 0x80000000000000e4 0x026295ffb0000000 0xfc0000000000037c 0x00731ffff0000000

def z67 : W := mkw 0x82695290003123ee 0x02d493ffbda802a8 0xfffffff8003ffbcf 0x87fc03fffff803f8

def z68 : W := mkw 0xb38e9d2f65464cf1 0xe1bffc55837bfd56 0xf3fffffffffffffb 0xfffffc7f8fffffff

def z69 : W := mkw 0xa002040941444c81 0x0008c8448010c912 0x000f00380701c081 0x040ce0660018e198

def z70 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xfff001c0383e3d0c 0x18730399f8e70267

def z71 : W := mkw 0x0000000000000060 0x0062151920000000 0x0000000000000050 0x00701c1800000000

def z72 : W := mkw 0x01868d2724000010 0x212b6c0002536c00 0x00000007ffc00030 0x6003fc000007fc00

def z73 : W := mkw 0x80000000000000e4 0x02d491ffb0000000 0xfc000000000003cc 0x03fc03fff0000000

def z74 : W := mkw 0x401000008008030a 0x0000020048040201 0x03f00007f83e0402 0x5800000008070207

def z75 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0x000f1e3807c1f8d1 0xa40cfc7e0018fdf8

def z76 : W := mkw 0x0000000000000000 0x020000a000000000 0x0000000000000388 0x038003e000000000

def z77 : W := mkw 0x80000000000000f4 0x00fedd5fa0000000 0xf0000000000002f8 0x007cfc7f80000000

def z78 : W := mkw 0x80000000000000e0 0x0008d85580000000 0xf0000000000002f8 0x000cfc7f80000000

def z79 : W := mkw 0x2000000040040081 0x0301a0e090008102 0xfc0f0007c73fc7af 0x5b83e3e1f000e387

def z80 : W := mkw 0x0208100000000000 0x0094000001280000 0x03fffff8000003c3 0x83fc00000ff80000

def z81 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0xf0000007c7c00430 0x7800fc018000fc07

def z82 : W := mkw 0x0080080200000000 0x0022040000420400 0x03f01fc7f8c00372 0xe0731c0008e71c00

def z83 : W := mkw 0x0104000400000000 0x0000000002012000 0x03ffe007ff000003 0x400000000f07e000

def z84 : W := mkw 0x0000000000000000 0x0008480000000000 0x00000000000002f0 0x000cfc0000000000

def z85 : W := mkw 0x004100000020030a 0x000002000c000280 0x03ffe000003fc003 0x000000000f000380

def z86 : W := mkw 0x006142900031230a 0x024003aa0c8002a8 0x00000000003ff808 0x040003fe000003f8

def z87 : W := mkw 0x80000000000000f4 0x012bfc55b0000000 0xfc00000000000034 0x0003fc01f0000000

def z88 : W := mkw 0x0000000000000010 0x01b7240000000000 0x0000000000000100 0x03f3000000000000

def z89 : W := mkw 0x1080080200020060 0xc022141100421444 0xf3f01fc7f8fe3f7a 0xf8731c1988e71e67

def z90 : W := mkw 0x14a00a4208921000 0xc800000000c21464 0x00001fc000c03800 0xa000000000e01c60

def z91 : W := mkw 0x938e9d2f25424c70 0xe1bf7c15037b7c54 0x03ffffffffc03bf3 0xe7fffc1e0ffffc78

def z92 : W := mkw 0x828a9d2324000074 0x20fe5d1f217a4c00 0x00001ff800c00050 0xa07c1c1e00f81c00

def z93 : W := mkw 0xb002040941464cf5 0xc39df8f79010d956 0xf00f1e3fc7fffefb 0xff8cfc7f8018ffff

def z94 : W := mkw 0x026952900031230a 0x000002000da802a8 0x03fffff8003ff803 0x840000000ff803f8

def z95 : W := mkw 0x3002040941464c01 0xc00848000010d956 0x000f1e3fc7fffef3 0xfc0cfc000018ffff

def z96 : W := mkw 0x8000000000000074 0x00fe5d1f20000000 0x0000000000000050 0x007c1c1e00000000

def z97 : W := mkw 0xf916240dd34ecce1 0xd109f855d215f957 0xfc000007ffc00434 0x7803fc01f007fc07

def z98 : W := mkw 0x68102000d20c8081 0x10008040d0048103 0xfc00000000000404 0x18000001f0000007

def z99 : W := mkw 0x0000000000000000 0x0000000000000000 0x03f00007f8000322 0x4003000008070000

def z100 : W := mkw 0x14a00a4208921060 0xc862151920c21464 0x00001fc000c03850 0xa0701c1800e01c60

def z101 : W := mkw 0x401000008008030a 0x0000020048040201 0x0ff0000038000104 0x0003038078070000

def z102 : W := mkw 0x038c992624000010 0x21bf6c00036b2400 0x03f0e1c0380003f0 0x03fffc000fe70000

def z103 : W := mkw 0xf957240dd36ecfeb 0xd309faf5de15fbd7 0xfffffe3fffffffff 0xff8fffffff1fffff

def z104 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc00000000000134 0x03f3ff81f0000000

def z105 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xfc001fc000fe3c5c 0xb8701f99f0e01e67

def z106 : W := mkw 0xfbdfbd2ff76ecffb 0xf3bffef5df7fffd7 0xffffffffffffffff 0xffffffffffffffff

def z107 : W := mkw 0xd4b00a42889a13fe 0xcbfffffff8c61665 0xfff01fc7f8fe3ffe 0xfbfffffff8e71e67

def z108 : W := mkw 0x9002040901424ce0 0xc008d85580105854 0xf0001e3800c03af8 0xa40cfc7f80181c78

def z109 : W := mkw 0x44b00a428898130a 0x0800020048c60621 0x03f001c038000000 0x0000000008e70000

def z110 : W := mkw 0xa0000000400400f5 0x03fffdffb0008102 0xfc0f0007c73fc7ff 0x5bfffffff000e387

def z111 : W := mkw 0x2000000040040081 0x0000804080008102 0xf00f0007c73fc6ab 0x5800e0618000e387

def z112 : W := mkw 0x0228529000112000 0x00d4010a01a80028 0x000001c000000000 0x0070000000e00000

def z113 : W := mkw 0x03efdfb72431231a 0x21bf6e000ffb6ea8 0x03fffffffffffbf3 0xe7fffc000ffffff8

def z114 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x03f0e1c7ffc00130 0x63f3fc000fe7fc00

def z115 : W := mkw 0xf8532409d36ecfeb 0xd208daf5dc14dbd7 0xfc0f1e3fc7fffeff 0xfc0cfffff018ffff

def z116 : W := mkw 0x8000000000000084 0x020080e690000000 0x0000000000000000 0x0000006600000000

def z117 : W := mkw 0x0000000000000060 0x0040111920000000 0xfc0000000000000c 0x00000399f0000000

def z118 : W := mkw 0x038e9d2724000010 0x20be4c00037b6c00 0x03ffffffffc00053 0xe07c1c000ffffc00

def z119 : W := mkw 0x7df52a46dabe936b 0xd86217196ec7b7e7 0xffffffc7ffffff7f 0xf8731f99ffe7ffe7

def z120 : W := mkw 0x82081000000000f4 0x03fffdffb1280000 0xfffffff8000003ff 0x83fffffffff80000

def z121 : W := mkw 0xb1868d2f65464cf1 0xe12bfc558253fd56 0xf00f1e3ffffffefb 0xfc0ffc7f801fffff

def z122 : W := mkw 0x7ffd7ad6dabfb3eb 0xdbf7b7fbffefb7ef 0xffffffffffffffff 0xffffffffffffffff

def z123 : W := mkw 0x0000000000000080 0x0101a04090000000 0xfc00000000000024 0x0003e001f0000000

def z124 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0x03f0e1c000000100 0x03f003800fe00000

def z125 : W := mkw 0x80000000000000f4 0x03ddf9ffb0000000 0xfc0000000000008c 0x038ce3fff0000000

def z126 : W := mkw 0x038e9d2724000000 0x20000000037b6c00 0x03ffffffffc00003 0xe00000000ffffc00

def z127 : W := mkw 0x838c9926240000f4 0x23fffdffb36b2400 0xfff0e1c0380003fc 0x03ffffffffe70000

def z128 : W := mkw 0x0000000000000000 0x0000000000000000 0xf0000007c03e062a 0x5800000180000207

def z129 : W := mkw 0x6bdfbd27f62c831b 0x31bf6e004f7fef83 0x03ffffffffffc7f3 0xfbfffc000fffff87

def z130 : W := mkw 0x54900842888a1060 0xc822141160461445 0xfc001e07f8fe3e7e 0xf8031c19f0071e67

def z131 : W := mkw 0x7df52a46dabe93eb 0xdb63b7f9fec7b7e7 0xffffffc7ffffffff 0xfbf3fff9ffe7ffe7

def z132 : W := mkw 0x4b7d72949239a30a 0x13d523aa5fad22a9 0x0ffffff8383ffbcf 0x87ff03fe7fff03f8

def z133 : W := mkw 0x002002000010030a 0x0040030808800220 0x03f01fc0003e3b4a 0x8070039808e00260

def z134 : W := mkw 0x0000000000000000 0x0040010800000000 0x0000000000000348 0x0070039800000000

def z135 : W := mkw 0x44b00a428898130a 0x0862070868c60621 0x0ff001c038000104 0x0073038078e70000

def z136 : W := mkw 0xf4b20e4bc9de5feb 0xc86adf5de8d6df77 0xffff1fffffffffff 0xfc7ffffff8ffffff

def z137 : W := mkw 0x0208100000000000 0x0094000001280000 0x000fe03800000081 0x038c000007180000

def z138 : W := mkw 0x0000000000000000 0x0094000000000000 0x00000000000003c0 0x03fc000000000000

def z139 : W := mkw 0x002002000010030a 0x0040030808800220 0x00000000003e3808 0x0000039800000260

def z140 : W := mkw 0xb022060941564feb 0xc048db5d8890db76 0xf3ff1fffc7fffffb 0xfc7cffff88f8ffff

def z141 : W := mkw 0x0000000000000000 0x0022040000000000 0x0000000000000370 0x00731c0000000000

def z142 : W := mkw 0xe9552004d22c83ff 0x13fffffffe05a383 0xffffe007ff3fc7ff 0x5bffffffff07e387

def z143 : W := mkw 0x44b00a428898130a 0x0862070868c60621 0x0ff01fc7f8c00376 0xe0731f8078e71c00

def z144 : W := mkw 0x56f95ad288bb336a 0xc86217196dee16ed 0xfffffffff8ffff7f 0xfc731f99ffff1fff

def z145 : W := mkw 0x038c992624000010 0x21b72400036b2400 0x03fffff8380003c3 0x83ff00000fff0000

def z146 : W := mkw 0xb002040941464cf5 0xc3fffdffb010d956 0xfc000007c7c007fc 0x7bfffffff000fc07

def z147 : W := mkw 0x54300240889a130a 0xc800020048841265 0x00000000003e3c00 0x1800000000000267

def z148 : W := mkw 0x026952900031230a 0x009402000da802a8 0x03fffff8003ffbc3 0x87fc00000ff803f8

def z149 : W := mkw 0x0000000000000004 0x024001aa30000000 0x0c00000000000004 0x0000038070000000

def z150 : W := mkw 0x0945200412208000 0x130120a016012080 0x0000e00000000000 0x0380000007000000

def z151 : W := mkw 0x0000000000000060 0x02f615bb20000000 0xfc000000000003fc 0x03ff1ffff0000000

def z152 : W := mkw 0x6bdfbd27f62c838b 0x3301a2e0df7fef83 0xffffffffffffc7af 0xfb83e3e1ffffff87

def z153 : W := mkw 0x3002040941464c01 0xc00000000010d956 0x00000007c7c00400 0x780000000000fc07

def z154 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0x000fe038003ff889 0x078c03fe071803f8

def z155 : W := mkw 0x006142900031230a 0x02d403aa0c8002a8 0x00000000003ffbc8 0x07fc03fe000003f8

def z156 : W := mkw 0x0002040100000010 0x01bf6c0000104800 0x000f1e3fc7c003f3 0xe3fffc000018fc00

def z157 : W := mkw 0xb38e9d2f65464ce1 0xe008d855837bfd56 0xf3fffffffffffefb 0xfc0cfc7f8fffffff

def z158 : W := mkw 0x038e9d2724000090 0x23bfece0937b6c00 0xffffffffffc003ff 0xe3ffffe1fffffc00

def z159 : W := mkw 0x026952900031238a 0x03d5a3ea9da802a8 0xfffffff8003ffbef 0x87ffe3fffff803f8

def z160 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z161 : W := mkw 0x6b5d7094d22da38b 0x1395a2e2df2da38b 0xffffe03fff3fc7af 0x5f8fe3e7ff1fe39f

def z162 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0xf0000007c7c006f8 0x780cfc7f8000fc07

def z163 : W := mkw 0xb002040941464ce5 0xc248d9ffb010d956 0xfc0f1e3fc7fffeff 0xfc0cfffff018ffff

def z164 : W := mkw 0x0000000000000014 0x03ff6daa30000000 0x0c000000000003f4 0x03ffff8070000000

def z165 : W := mkw 0xa947240d5364cc81 0x1309e8e49611e992 0x000fe0380701c081 0x078ce0660718e198

def z166 : W := mkw 0x80020401000000e0 0x0008d85580104800 0xf00f1e3fc7c002fb 0xe00cfc7f8018fc00

def z167 : W := mkw 0xd4b00a42889a13ee 0xca6297fff8c61665 0xfff01fc7f8fe3f7e 0xf8731ffff8e71e67

def z168 : W := mkw 0x0000000000000080 0x020080e090000000 0xfc0000000000000c 0x000003e1f0000000

def z169 : W := mkw 0x3002040941464c01 0xc00000000010d956 0x000f1e3fc7fffc03 0xfc0000000018ffff

def z170 : W := mkw 0x401000008008030a 0x0000020048040201 0xfff00007f83e072e 0x58030381f8070207

def z171 : W := mkw 0xf4b20e4bc9de5feb 0xc808da55c8d6df77 0xf3ff1ffffffffefb 0xfc0cfc7f88ffffff

def z172 : W := mkw 0x0208100000000000 0x0094000001280000 0x03fffff8003ffbcb 0x87fc007e0ff803f8

def z173 : W := mkw 0x0269529000312000 0x02d401aa05a800a8 0x000ffff80001f8c1 0x87fc007e07f801f8

def z174 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0x03f01fc7f8fe3c52 0xf8701c1808e71e67

def z175 : W := mkw 0xb002040941464ce1 0xc309f8f59010d956 0xfc0f1e3fc7ffffff 0xff8ffffff018ffff

def z176 : W := mkw 0x80000000000000f4 0x01bffc55b0000000 0xfc000000000003f4 0x03fffc01f0000000

def z177 : W := mkw 0x80000000000000f4 0x03f7b5ffb0000000 0xfc0000000000010c 0x03f303fff0000000

def z178 : W := mkw 0x495520049228830a 0x130122a05e052281 0x0fffe007ff0003a7 0x4383e3807f07e000

def z179 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xfff0e007ff000524 0x5b83e381ff07e007

def z180 : W := mkw 0x036fd7b52431231a 0x23dd6baa0fb96aa8 0x03fffff8073ffbcb 0x87fce3fe0ff8e3f8

def z181 : W := mkw 0x80000000000000f4 0x036bfdffb0000000 0xfc0000000000003c 0x0003fffff0000000

def z182 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x000fe03fffc000b1 0x638ffc00071ffc00

def z183 : W := mkw 0x69142004d20c838b 0x1101a240da05a303 0xfff00007ff3e072e 0x5803e381f807e207

def z184 : W := mkw 0x0249509000212000 0x029400a205280088 0x000fe0380001c081 0x078c006607180198

def z185 : W := mkw 0xb26b569941776feb 0xc2dcdbff8db8dbfe 0xf3ffffffc7fffffb 0xfffcffff8ff8ffff

def z186 : W := mkw 0x7d752244dabe93eb 0xdb41b3f9fe85b3e7 0xffffe007ff3fffaf 0x5b83e3f9ff07e3e7

def z187 : W := mkw 0x80000000000000f0 0x01bffc5580000000 0xf0000000000003f8 0x03fffc7f80000000

def z188 : W := mkw 0x0000000000000000 0x0062050820000000 0x0c00000000000104 0x0073038070000000

def z189 : W := mkw 0x69756294d23da38b 0x1341a3eade85a3ab 0xffffe007ff3fffaf 0x5f83e3ffff07e3ff

def z190 : W := mkw 0x54900842888a1060 0xc822141160461445 0xfc000007f8c00434 0x78031c01f0071c07

def z191 : W := mkw 0x69552004d22c8081 0x1301a0e0d605a183 0xfc0fe007ff01c4a5 0x5b83e061f707e187

def z192 : W := mkw 0x80000000000000f4 0x016bfd5db0000000 0xfc0000000000037c 0x0073ff99f0000000

def z193 : W := mkw 0xb26b569941776feb 0xc008da558db8dbfe 0xf3ffffffc7fffefb 0xfc0cfc7f8ff8ffff

def z194 : W := mkw 0x44b00a428898130a 0x0862070868c60621 0x0ff01fc0383e3b4e 0x8073039878e70260

def z195 : W := mkw 0x6b7d7294d23da38b 0x1301a2e0dfada3ab 0xffffffffff3fffaf 0xdf83e3e1ffffe3ff

def z196 : W := mkw 0x409008028008030a 0x0022060048460601 0xfff01fc7f8fe077e 0xf8731f81f8e71e07

def z197 : W := mkw 0x0002040100000000 0x0008480000104800 0x000f1e3fc7c002f3 0xe00cfc000018fc00

def z198 : W := mkw 0xb38e9d2f65464cf5 0xe3fffdffb37bfd56 0xffffffffffffffff 0xffffffffffffffff

def z199 : W := mkw 0x0000000000000000 0x0000000000000000 0x03ffe00000000383 0x038000000f000000

def z200 : W := mkw 0x8000000000000094 0x03dde9ee90000000 0x00000000000003c8 0x03fce3fe00000000

def z201 : W := mkw 0x02ebdfb32431231a 0x22fe4faa0dfa4ea8 0x03fffff800fffbdb 0xa7fc1ffe0ff81ff8

def z202 : W := mkw 0x8000000000000064 0x0040111f20000000 0x0000000000000000 0x0000001e00000000

def z203 : W := mkw 0x6bddb926f62c839b 0x33b7a6e0df6fa783 0xffffe1c7ff3fc7af 0x5bf3e3e1ffe7e387

def z204 : W := mkw 0x81868d27240000f4 0x23fffdffb2536c00 0xfc000007ffc003fc 0x63fffffff007fc00

def z205 : W := mkw 0x0000000000000000 0x00d4010a00000000 0x0000000000000040 0x007c001e00000000

def z206 : W := mkw 0xb000000841464ce1 0xc000905580009156 0xf0000000003ffc08 0x1c00007f800003ff

def z207 : W := mkw 0x56f95ad288bb330a 0xc80002004dee16ed 0x03fffffff8fffc03 0xfc0000000fff1fff

def z208 : W := mkw 0x7cf12a42dabe93eb 0xda6297f9fcc697e7 0xfff01fc7f8ffff7e 0xf8731ff9f8e71fe7

def z209 : W := mkw 0xf955200cd36ecfeb 0xd301b2f5de05b3d7 0xffffe007ff3fffaf 0x5f83e3ffff07e3ff

def z210 : W := mkw 0x026952900031230a 0x00d4030a0da802a8 0x03fffff8003ff843 0x847c001e0ff803f8

def z211 : W := mkw 0x006142900031230a 0x024003aa0c8002a8 0x03ffe000003ffb8b 0x078003fe0f0003f8

def z212 : W := mkw 0x90000000000200f4 0xc3fffdffb0001044 0xfc001e07c0fe3ffe 0xfbfffffff0001e67

def z213 : W := mkw 0x16a85ad208933060 0xc8f6151b21ea146c 0x00001ff800c03850 0xa47c1c1e00f81c78

def z214 : W := mkw 0x0041000000200000 0x020000a004000080 0x000fe0000001c081 0x0380006007000180

def z215 : W := mkw 0x0228529000112000 0x00d4010a01a80028 0x03fffff800003bc3 0x87fc001e0ff80078

def z216 : W := mkw 0x0208100000000000 0x0094000001280000 0x03f0e1c000000100 0x03f000000fe00000

def z217 : W := mkw 0xb3efdfbf65776ffb 0xe3ffffff8ffbfffe 0xf3fffffffffffffb 0xffffffff8fffffff

def z218 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xffff1ffff8ffffff 0xfc7f1ffff8ff1fff

def z219 : W := mkw 0x495520049228830a 0x130122a05e052281 0x0fffe000383fc38f 0x038303e07f070380

def z220 : W := mkw 0x4bdfbd27b628831a 0x33bf6ea05f7f6e81 0x0fffffffffc003f7 0xe3ffff807ffffc00

def z221 : W := mkw 0xb000000841464ce5 0xc24091ffb0009156 0xfc000000003ffc0c 0x1c0003fff00003ff

def z222 : W := mkw 0x0000000000000000 0x0000000000000000 0x000f0007c70002a3 0x4000e0000000e000

def z223 : W := mkw 0x7df52a46dabe930b 0xd80002004ec7b7e7 0x03ffffc7fffffc03 0xf80000000fe7ffe7

def z224 : W := mkw 0x16e95ad208b3336a 0xcaf617bb2dea16ec 0x03fffff800fffbdb 0xa7fc1ffe0ff81ff8

def z225 : W := mkw 0x026952900031230a 0x000002000da802a8 0x03f0e1c000000000 0x000000000fe00000

def z226 : W := mkw 0xb063469941776feb 0xc248dbff8c90dbfe 0xf00f1e3fc7fffefb 0xfc0cffff8018ffff

def z227 : W := mkw 0x69142004d20c8081 0x1101a040d205a103 0xfc000007ff000424 0x5803e001f007e007

def z228 : W := mkw 0x028a9d2324000010 0x20be4c00017a4c00 0x03fffff800c003d3 0xa3fc1c000ff81c00

def z229 : W := mkw 0x6bdfbd27f62c830b 0x300002004f7fef83 0x03ffffffffffc403 0xf80000000fffff87

def z230 : W := mkw 0xb002040941464ce1 0xc06add5da010d956 0xfc0f1e3fc7ffffff 0xfc7ffffff018ffff

def z231 : W := mkw 0xd4300240889a13ee 0xca4093fff8841265 0xfc000000003e3c0c 0x180003fff0000267

def z232 : W := mkw 0x0000000000000014 0x039520a210000000 0x0000000000000000 0x0380000000000000

def z233 : W := mkw 0x82285290001120f4 0x03fffdffb1a80028 0xfc001ff800003bfc 0x87fffffff0f80078

def z234 : W := mkw 0x54b00a42889a130a 0xc822060048c61665 0x03f01fc7f8fe3f72 0xf8731c0008e71e67

def z235 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0x03f0e1c0003ff908 0x07f003fe0fe003f8

def z236 : W := mkw 0x030e952524000010 0x21bf6c0003396800 0x000fe038070003f1 0x03fffc000718e000

def z237 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x03ffe1f83f000181 0x03ffe0000fffe000

def z238 : W := mkw 0x68512000d22c830b 0x100002004c048383 0x00000000003fc400 0x1800000000000387

def z239 : W := mkw 0xb26b569941776fff 0xc3ffffffbdb8dbfe 0xffffffffc7ffffff 0xfffffffffff8ffff

def z240 : W := mkw 0x30000000400600e1 0xc000905180009146 0xf00f1e07c7fffefb 0xf800fc798000ffe7

def z241 : W := mkw 0x2002040941444c01 0x000000000010c912 0x000f00380701c001 0x040000000018e198

def z242 : W := mkw 0x1002040100020060 0xc008581100105844 0xf00f1e3fc7fe3efb 0xf80cfc198018fe67

def z243 : W := mkw 0xb002040941464ce1 0xc00090558010d956 0xf00f1e3fc7fffc0b 0xfc00007f8018ffff

def z244 : W := mkw 0x7c712240dabe93eb 0xda4093f9fc8493e7 0xfc000000003ffc0c 0x180003f9f00003e7

def z245 : W := mkw 0x495520049228831e 0x13f727aa7e052281 0x0ff0e00038000104 0x03f303807f070000

def z246 : W := mkw 0x82495090002120f4 0x03fffdffb5280088 0xfc0fe0380001c3fd 0x07fffffff7180198

def z247 : W := mkw 0x6996ad27f60c8091 0x312bec40d257ed03 0xfc000007ffc00434 0x7803fc01f007fc07

def z248 : W := mkw 0xb1868d2f65464cf1 0xe12bfc558253fd56 0xf0000007ffc00430 0x7803fc018007fc07

def z249 : W := mkw 0x7df52a46dabe938b 0xdb01a2e0dec7b7e7 0xffffffc7ffffffaf 0xfb83e3e1ffe7ffe7

def z250 : W := mkw 0x002002000010030a 0x0040030808800220 0x03ff1ff8003ffbcb 0x847c03fe08f803f8

def z251 : W := mkw 0x0104000400000000 0x0101200002012000 0x03ffe007ff0003a3 0x4383e0000f07e000

def z252 : W := mkw 0xb000000841464ce1 0xc008d85580009156 0xf0000000003ffef8 0x1c0cfc7f800003ff

def z253 : W := mkw 0x0288992224000010 0x20b60400016a0400 0x000001c000000000 0x0070000000e00000

def z254 : W := mkw 0x028a9d2324000010 0x20be4c00017a4c00 0x00001ff800c00050 0xa07c1c0000f81c00

def z255 : W := mkw 0x68512000d22c838b 0x120082e0dc048383 0xfc000000003fc40c 0x180003e1f0000387

def z256 : W := mkw 0x54300240889a136a 0xc862171968841265 0xfc000000003e3f7c 0x18731f99f0000267

def z257 : W := mkw 0x026952900031230a 0x004003080da802a8 0x03fffff8003ffb4b 0x847003980ff803f8

def z258 : W := mkw 0x02aadfb324112010 0x20fe4d0a01fa4c28 0x00001ff800c03850 0xa47c1c1e00f81c78

def z259 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001e00003e3a4a 0x8000001800000260

def z260 : W := mkw 0x46f95ad288b9330a 0x0af607aa6dee06a9 0x0ff0e1c038000104 0x03f303807fe70000

def z261 : W := mkw 0x030e952524000010 0x219d680003396800 0x03ffe03fff0003a3 0x438fe0000f1fe000

def z262 : W := mkw 0x002002000010030a 0x02d403aa08800220 0x03f01fc0003e3bca 0x83fc03fe08e00260

def z263 : W := mkw 0x0000000000000000 0x030120a010000000 0x0c00000000000104 0x0383038070000000

def z264 : W := mkw 0xf957240dd36ecfeb 0xd008da55ce15fbd7 0xf3fffe3ffffffefb 0xfc0cfc7f8f1fffff

def z265 : W := mkw 0x69d7ad27f62c839b 0x332beee0de57ef83 0xffffe007ffffc7bf 0x7b83ffe1ff07ff87

def z266 : W := mkw 0x126952900033236a 0xc2d413bb0da812ec 0xf3ffffffc0fffffb 0xfffc1fff8ff81fff

def z267 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0x0ff01fc038c03954 0xa0731f9878e71c60

def z268 : W := mkw 0xa002040941444c95 0x039de8e69010c912 0x000f00380701c081 0x078ce0660018e198

def z269 : W := mkw 0x8000000000000074 0x03ff7dbf30000000 0x0c00000000000154 0x03ff1f9e70000000

def z270 : W := mkw 0x69752204d23c838b 0x1341a3e8de85a3a3 0xffffffc7ff3fffef 0xdbf3e3f9ffe7e3e7

def z271 : W := mkw 0xb22a569941576ce1 0xc0dcd95f81b8d97e 0xf00f1fffc7fffefb 0xfc7cfc7f80f8ffff

def z272 : W := mkw 0x80614290003123ee 0x024093ffbc8002a8 0xfc000000003ff80c 0x040003fff00003f8

def z273 : W := mkw 0x2002040140040081 0x0008c8408010c902 0xf00f1e3fc7ffc6fb 0xf80cfc618018ff87

def z274 : W := mkw 0x828a9d23240000f4 0x23fffdffb17a4c00 0xfc001ff800c003fc 0xa3fffffff0f81c00

def z275 : W := mkw 0x0249509000212000 0x029400a205280088 0x000ffe38003ffacb 0x878c007e071803f8

def z276 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0x03f0ffc0003e3b4a 0x83f003980fe00260

def z277 : W := mkw 0x020a140100000000 0x009c480001384800 0x03ffffffc7c003f3 0xe3fcfc000ff8fc00

def z278 : W := mkw 0xb002040941464c61 0xc00858150010d956 0x000f1e3fc7fffc53 0xfc0c1c1e0018ffff

def z279 : W := mkw 0x7957240dd36ecf0b 0xd00002004e15fbd7 0x03fffe3ffffffc03 0xfc0000000f1fffff

def z280 : W := mkw 0x03cfddb724212010 0x23bf6ca2077b6c88 0x03ffffffffc1c3f3 0xe7fffc660ffffd98

def z281 : W := mkw 0x54900842888a1060 0xc862151960461445 0xfc000007f8c0077c 0x78731f99f0071c07

def z282 : W := mkw 0x038e9d2724000000 0x20940000037b6c00 0x03ffffffffc003c3 0xe3fc00000ffffc00

def z283 : W := mkw 0xc4b00a42889813fe 0x0bfffffff8c60621 0xfff001c0380003fc 0x03fffffff8e70000

def z284 : W := mkw 0x56b81a42889a136a 0xc8f6171969ee1665 0xfffffffff8fe3fff 0xfbff1f99ffff1e67

def z285 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000000002c8 0x000c007e00000000

def z286 : W := mkw 0xa30e952d65444c91 0x219de8448339e912 0x000fe0380701c081 0x078ce0660718e198

def z287 : W := mkw 0xa002040941444ce1 0x0008d8558010c912 0xf00f00380701c2f9 0x040cfc7f8018e198

def z288 : W := mkw 0x57bc9b66ac9a137a 0xe9f737196bef3665 0xfff0ffc7f8fe3f7e 0xfbf31f99ffe71e67

def z289 : W := mkw 0x002002000010030a 0x0040030808800220 0x03f001c000000100 0x0070038008e00000

def z290 : W := mkw 0x6b7d7294d23da38b 0x13d5a3eadfada3ab 0xffffe1c7ff3fc7af 0x5bf3e3e1ffe7e387

def z291 : W := mkw 0x0000000000000090 0x03bfece090000000 0xfc000000000003fc 0x03ffffe1f0000000

def z292 : W := mkw 0xc0100000800803fe 0x03fffffff8040201 0xfff00007f83e07fe 0x5bfffffff8070207

def z293 : W := mkw 0xfdf72e4fdbfedfeb 0xdb6bfffdfed7fff7 0xffffffffffffffff 0xffffffffffffffff

def z294 : W := mkw 0x0000000000000080 0x0301a0e090000000 0x0000000000000080 0x0380e06000000000

def z295 : W := mkw 0xe9552004d22c839f 0x139deae6de05a383 0xffffe007ff3fc7af 0x5b8fe3e7ff07e387

def z296 : W := mkw 0x57be9f67ac9a130a 0xe80002004bff7e65 0x03fffffffffe3c03 0xf80000000ffffe67

def z297 : W := mkw 0x2b4fb52576248091 0x339de8e09739e982 0x000fe0380701c081 0x038ce0600718e180

def z298 : W := mkw 0x427952908039230a 0x02d403aa4dac02a9 0xfffffffff83fffef 0xdfff03ffffff03ff

def z299 : W := mkw 0x0000000000000060 0x0000101100000000 0xf000000000000278 0x00001c1980000000

def z300 : W := mkw 0x69552004d22c838b 0x10008240ce05a383 0xf3ffe007ff3fc6ab 0x5800e0618f07e387

def z301 : W := mkw 0x002002000010030a 0x0000020008800220 0x03f01fc0003e3802 0x8000000008e00260

def z302 : W := mkw 0xa24b549941656c81 0x029cc8e68538c99a 0x000fe0380701c081 0x078ce0660718e198

def z303 : W := mkw 0x57be9f67ac9a131a 0xe9bf6e004bff7e65 0x03fffffffffe3ff3 0xfbfffc000ffffe67

def z304 : W := mkw 0xb28a9d2b65464cf1 0xe0bedc55817add56 0xf00f1fffc7fffefb 0xfc7cfc7f80f8ffff

def z305 : W := mkw 0x69572405d22c838b 0x1309eae0de15eb83 0xfffffe3fffffc7ff 0xfb8fffe1ff1fff87

def z306 : W := mkw 0xa0000000400400e1 0x0008d85580008102 0xf00f0007c73fc6fb 0x580cfc7f8000e387

def z307 : W := mkw 0x80000000000000f4 0x01fffd5fb0000000 0xfc00000000000074 0x007ffc1ff0000000

def z308 : W := mkw 0x0208100000000000 0x02d401aa01280000 0x03fffff8000003cb 0x83fc03fe0ff80000

def z309 : W := mkw 0x9002040901424c60 0xc008581500105854 0x00001e3800c03850 0xa40c1c1e00181c78

def z310 : W := mkw 0x026952900031230a 0x029402a20da802a8 0x03fffff8003ff883 0x878c00660ff803f8

def z311 : W := mkw 0x038c992624000000 0x20000000036b2400 0x03f0e1c038000000 0x000000000fe70000

def z312 : W := mkw 0x80000000000000e0 0x0008d85580000000 0xf00f1e38003ffafb 0x840cfc7f801803f8

def z313 : W := mkw 0x3000000841464c01 0xc000000000009156 0x00000000003ffc00 0x1c000000000003ff

def z314 : W := mkw 0x80000000000000e4 0x0248d9ffb0000000 0xfc000000000002fc 0x000cfffff0000000

def z315 : W := mkw 0x83efdfb7243123fe 0x23ffffffbffb6ea8 0xfffffffffffffbff 0xe7fffffffffffff8

def z316 : W := mkw 0x54900842888a136a 0xc822161168461645 0xfff00007f8fe073e 0x78031f81f8071e07

def z317 : W := mkw 0x69552004d22c839f 0x13f7a7eafe05a383 0xffffe007ff3fc7af 0x5bf3e3e1ff07e387

def z318 : W := mkw 0x000000000000030a 0x0000020008000200 0x03f00000003e030a 0x0000038008000200

def z319 : W := mkw 0x0000000000000000 0x0000000000000000 0x000f1e38000002c3 0x800c000000180000

def z320 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xfc0fe000073fc48d 0x1b80e3e1f700e387

def z321 : W := mkw 0x7d942846da8e90e1 0xd923b451f247b547 0xfc000007ffc00434 0x7803fc01f007fc07

def z322 : W := mkw 0x80000000000000e4 0x0341b1ffb0000000 0xfc000000000003ac 0x0383e3fff0000000

def z323 : W := mkw 0x54b00a42889a137a 0xc9ff7f1968c61665 0xfff01fc7f8fe3ffe 0xfbffff99f8e71e67

def z324 : W := mkw 0x024950900021230a 0x029402a20d280288 0x03ffe038003fc38b 0x078c03e60f180398

def z325 : W := mkw 0x9002040901424c74 0xc0fe5d1f20105854 0x00001e3800c03850 0xa47c1c1e00181c78

def z326 : W := mkw 0x1000000000020060 0xc000101100001044 0xf0000007c0c00430 0x78001c0180001c07

def z327 : W := mkw 0xf4920c4bc9ce5ce1 0xc82adc55e056dd57 0xfc0f1e3ffffffeff 0xfc0ffc7ff01fffff

def z328 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0x03fffff8000003c3 0x83fc03800ff80000

def z329 : W := mkw 0x69142004d20c8001 0x100000004205a103 0x00000007ff000400 0x580000000007e007

def z330 : W := mkw 0x8000000000000060 0x0008581500000000 0x0000000000000050 0x000c1c1e00000000

def z331 : W := mkw 0xa26b569941756f8b 0x02dccbee8db8cbba 0x03fffff8073ffbcb 0x87fce3fe0ff8e3f8

def z332 : W := mkw 0x7dd52846daae93eb 0xdb23b6f1fe47b7c7 0xffffe007ffffc7bf 0x7b83ffe1ff07ff87

def z333 : W := mkw 0xa000000841444c81 0x0000804480008112 0x000000000001c000 0x0400006600000198

def z334 : W := mkw 0x94a00a42089210f4 0xcbfffdffb0c21464 0xfc001fc000c03bfc 0xa3fffffff0e01c60

def z335 : W := mkw 0x8000000000000094 0x039de8e690000000 0xfc000000000003ac 0x038fe3e7f0000000

def z336 : W := mkw 0x0000000000000074 0x03f735bb30000000 0xfc0000000000037c 0x03f31f99f0000000

def z337 : W := mkw 0x026952900031231e 0x03f727aa3da802a8 0x0ff0e1c000000104 0x03f303807fe00000

def z338 : W := mkw 0x028a9d2324000010 0x21bf6c00017a4c00 0x00001ff800c003f0 0xa3fffc0000f81c00

def z339 : W := mkw 0x0184892624000010 0x2123240002432400 0x0000000038000000 0x0003000000070000

def z340 : W := mkw 0x830e9525240000f4 0x23fffdffb3396800 0xfc0fe038070003fd 0x03fffffff718e000

def z341 : W := mkw 0xb000000841464ce1 0xc000905580009156 0xf0001e07c0fffe7a 0xfc001c7f80001fff

def z342 : W := mkw 0xf4b00a4ac9de5feb 0xc862975de8c69777 0xfff01fc7f8ffff7e 0xfc731ffff8e71fff

def z343 : W := mkw 0xe8512000d22c83ef 0x124093fffc048383 0xfc000000003fc40c 0x180003fff0000387

def z344 : W := mkw 0x026952900031230a 0x020002a00da802a8 0x03fffff8003ffb8b 0x878003e00ff803f8

def z345 : W := mkw 0x0080080200000000 0x0000000000420400 0x03f01fc7f8c00002 0xe000000008e71c00

def z346 : W := mkw 0x0104000400000010 0x01bf6c0002012000 0x03ffe007ff0003f3 0x43fffc000f07e000

def z347 : W := mkw 0x03ae9f272410031a 0x21ff6f080bfb6e20 0x03fffffffffe3bfb 0xe3ffff980ffffe60

def z348 : W := mkw 0x69142004d20c8081 0x1101a040d205a103 0xfc0f0007ff3fc6af 0x5803e061f007e387

def z349 : W := mkw 0x006142900031230a 0x000002000c8002a8 0x00000000003ff800 0x04000000000003f8

def z350 : W := mkw 0x0000000000000000 0x02d401aa00000000 0x0000000000000100 0x03f0038000000000

def z351 : W := mkw 0x54900842888a1060 0xc822141160461445 0xfff01fc7f8c00776 0xf8731c01f8e71c07

def z352 : W := mkw 0x0002040100000000 0x0008480000104800 0x000f003807000081 0x000ce0000018e000

def z353 : W := mkw 0x4bddb926b628831a 0x33b726a05f6f2681 0x0ff0e1c038000104 0x03f303807fe70000

def z354 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x000ffff807c000d1 0xa3fcfc0007f8fc00

def z355 : W := mkw 0x80000000000000f4 0x039df8f790000000 0xf0000000000002f8 0x038cfc7f80000000

def z356 : W := mkw 0xd4b00a42889a137e 0xc8fe5f1f68c61665 0xfff01fc7f8fe3f7e 0xf87f1f9ff8e71e67

def z357 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x00001fffffc00070 0xe07ffc0000fffc00

def z358 : W := mkw 0x0000000000000010 0x00be4c0000000000 0x0000000000000050 0x007c1c0000000000

def z359 : W := mkw 0x2000000040040081 0x0000804080008102 0xf0000007c7000420 0x5800e0018000e007

def z360 : W := mkw 0x0184080600000000 0x0123240002432400 0x03ffffc7ffc003f3 0xe3f3fc000fe7fc00

def z361 : W := mkw 0x80614290003123fe 0x03ffffffbc8002a8 0xfc000000003ffbfc 0x07fffffff00003f8

def z362 : W := mkw 0x68512000d22c838b 0x120082e0dc048383 0xffffe000003fc78f 0x1b8003e1ff000387

def z363 : W := mkw 0x69552004d22c838b 0x120082e0de05a383 0xffffe007ff3fc40f 0x580003e1ff07e387

def z364 : W := mkw 0x54b00a42889a130a 0xc862070868c61665 0x0ff01fc7f8fe3d06 0xf873038078e71e67

def z365 : W := mkw 0x7957240dd36ecf8b 0xd301a2e0de15fbd7 0xfffffe3fffffffaf 0xff83e3e1ff1fffff

def z366 : W := mkw 0x204100004024038b 0x020082e08c008382 0xf3ffe007c73fc7ab 0x5b80e3e18f00e387

def z367 : W := mkw 0x8000000000000094 0x03ffedeeb0000000 0x0c00000000000184 0x03ffe3e670000000

def z368 : W := mkw 0xb002040941464cf5 0xc12bfc55b010d956 0xfc000007c7c00434 0x7803fc01f000fc07

def z369 : W := mkw 0x0080080200000000 0x0022040000420400 0x00001fc000c00050 0xa0701c0000e01c00

def z370 : W := mkw 0x1000000000020060 0xc000101100001044 0xf0000000003e3c08 0x1800001980000267

def z371 : W := mkw 0xf957240dd36ecfeb 0xd309faf5de15fbd7 0xffffe007ffffc7bf 0x7b83ffe1ff07ff87

def z372 : W := mkw 0xe9552004d22c83ef 0x1341b3fffe05a383 0xffffe007ff3fc7af 0x5b83e3ffff07e387

def z373 : W := mkw 0x90000000000200e0 0xc008d85580001044 0xf0001e07c0fe3efa 0xf80cfc7f80001e67

def z374 : W := mkw 0xd4b00a42889a13ea 0xc86adf5de8c61665 0xfff01fc7f8fe3ffe 0xf87ffffff8e71e67

def z375 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xfc000007ff3fc42c 0x5803e3e1f007e387

def z376 : W := mkw 0xd4b00a42889a13fe 0xc96bff5df8c61665 0xfff01fc7f8fe3f7e 0xf873ff99f8e71e67

def z377 : W := mkw 0x038e9d2724000070 0x21ff7d19237b6c00 0xffffffffffc003ff 0xe3ffff99fffffc00

def z378 : W := mkw 0x495520049228830a 0x100002004e052281 0x03f0e00038000000 0x000000000f070000

def z379 : W := mkw 0x038e9d2724000010 0x219d6800037b6c00 0x03ffffffffc00083 0xe38ce0000ffffc00

def z380 : W := mkw 0x030e952524000010 0x219d680003396800 0x000ffe3fc7c002f3 0xe38cfc000718fc00

def z381 : W := mkw 0xa38e9d2f65444c91 0x21bfec44837bed12 0x03ffffffffc1c3f3 0xe7fffc660ffffd98

def z382 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0xf00f1e3fc7fffc33 0xfc00fc018018ffff

def z383 : W := mkw 0x47be9f67ac98131a 0x29ff6f086bff6e21 0x0fffffffffc003f7 0xe3ffff807ffffc00

def z384 : W := mkw 0x0208100000000000 0x0000000001280000 0x03fffff800000003 0x800000000ff80000

def z385 : W := mkw 0xd6f95ad288bb33fe 0xcbfffffffdee16ed 0xfffffffff8ffffff 0xffffffffffff1fff

def z386 : W := mkw 0x01868d2724000010 0x212b6c0002536c00 0x000f1e3fffc002f3 0xe00ffc00001ffc00

def z387 : W := mkw 0xf4b20e4bc9de5feb 0xc86adf5de8d6df77 0xfff01fc7fffe3f7e 0xf873ff99f8e7fe67

def z388 : W := mkw 0xf4300248c9de5feb 0xc840935de8849377 0xfc000000003ffc0c 0x1c0003fff00003ff

def z389 : W := mkw 0x14a00a4208921060 0xc862151920c21464 0xf0001fc7c0fe3e7a 0xf8701c1980e01e67

def z390 : W := mkw 0x54900842888a1000 0xc800000040461445 0x00000007f8c00400 0x7800000000071c07

def z391 : W := mkw 0x2000000040040081 0x0000804080008102 0xf0000000003fc408 0x1800006180000387

def z392 : W := mkw 0xf6fb5edbc9ff7feb 0xcafedfffedfedfff 0xffffffffffffffff 0xffffffffffffffff

def z393 : W := mkw 0x8000000000000074 0x002a5c1520000000 0x0000000000000010 0x00001c0000000000

def z394 : W := mkw 0x80000000000000e0 0x0008d85580000000 0xf000000000000030 0x0000fc0180000000

def z395 : W := mkw 0x69d52806d22c838b 0x1323a6e0de47a783 0xffffffc7ffffc7ff 0xfbf3ffe1ffe7ff87

def z396 : W := mkw 0x443002408898130a 0x0840030868840221 0x0c00000000000004 0x0000038070000000

def z397 : W := mkw 0xd4900842888a10f4 0xc92bfc55f0461445 0xfc000007f8c00434 0x7803fc01f0071c07

def z398 : W := mkw 0x401000008008036a 0x0062171968040201 0xfff00007f83e077e 0x58731f99f8070207

def z399 : W := mkw 0x038c992624000010 0x21b72400036b2400 0x03ffe1c7ff0003a3 0x43f3e0000fe7e000

def z400 : W := mkw 0x1000000000020060 0xc062151920001044 0xfc001e07c0fe3f7e 0xf8731f99f0001e67

def z401 : W := mkw 0x82695290003123fe 0x03ffffffbda802a8 0xfff0e1c0000003fc 0x03ffffffffe00000

def z402 : W := mkw 0xd7be9f67ac9a13fe 0xebfffffffbff7e65 0xfffffffffffe3fff 0xfbfffffffffffe67

def z403 : W := mkw 0x030e952524000010 0x219d680003396800 0x03fffff8070003c3 0x83fce0000ff8e000

def z404 : W := mkw 0xd4300240889a13fe 0xcbfffffff8841265 0xfc000000003e3ffc 0x1bfffffff0000267

def z405 : W := mkw 0x00000000000000e0 0x0363b5f9b0000000 0xfc000000000003fc 0x03f3fff9f0000000

def z406 : W := mkw 0x038e9d2724000000 0x20220400037b6c00 0x03ffffffffc00373 0xe0731c000ffffc00

def z407 : W := mkw 0x4914200492088000 0x1101200052052001 0x0c00000038000004 0x0003000070070000

def z408 : W := mkw 0x68512000d22c838b 0x120082e0dc048383 0xfff00007f83fc72e 0x580303e1f8070387

def z409 : W := mkw 0x038e9d2724000000 0x21012000037b6c00 0x03ffffffffc003a3 0xe383e0000ffffc00

def z410 : W := mkw 0xf4920c4bc9ce5ce1 0xc82adc55e056dd57 0xfc000007ffc00434 0x7803fc01f007fc07

def z411 : W := mkw 0x03efdfb72431230a 0x200002000ffb6ea8 0x03fffffffffff803 0xe40000000ffffff8

def z412 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000003ff808 0x0400007e000003f8

def z413 : W := mkw 0x56f95ad288bb336a 0xcaf617bb6dee16ed 0xfff0ffc7f8fe3f7e 0xfbf31f99ffe71e67

def z414 : W := mkw 0x026952900031230a 0x000002000da802a8 0x03fffff8003ffacb 0x840c007e0ff803f8

def z415 : W := mkw 0x0020020000100000 0x0040010800800020 0x00001fc000003840 0x8070001800e00060

def z416 : W := mkw 0x54b00a42889a136a 0xc800121148c61665 0xf3f01fc7f8fe3e7a 0xf8001c1988e71e67

def z417 : W := mkw 0x830e952524000094 0x239de8e693396800 0x000fe03807000081 0x038ce0660718e000

def z418 : W := mkw 0x0000000000000000 0x0101200000000000 0x00000000000003a0 0x0383e00000000000

def z419 : W := mkw 0x0000000000000080 0x0000804080000000 0xf0000000000002a8 0x0000e06180000000

def z420 : W := mkw 0x0000000000000000 0x02d401aa00000000 0x000f1e38003ffbcb 0x87fc03fe001803f8

def z421 : W := mkw 0xeb7d7294d23da3ff 0x13ffffffffada3ab 0xffffffffff3fffff 0xdfffffffffffe3ff

def z422 : W := mkw 0x028a9d2324000010 0x20be4c00017a4c00 0x03f01ffff8c00372 0xe07f1c0008ff1c00

def z423 : W := mkw 0x57ffdff7acbb337a 0xebff7fbb6fff7eed 0xffffffffffffffff 0xffffffffffffffff

def z424 : W := mkw 0xb000000841464ce1 0xc000905580009156 0xf000000000000400 0x1800000180000007

def z425 : W := mkw 0x54f14ad288bb336a 0xca6217bb6cc616ed 0xfff01fc7f8ffff7e 0xfc731ffff8e71fff

def z426 : W := mkw 0x6b9ebd27f60c8091 0x31bfec40d37fed03 0xffffffffffc007f7 0xfbfffc01fffffc07

def z427 : W := mkw 0x69552004d22c838b 0x13d5a3eade05a383 0xffffe007ff3fc7ef 0x5bffe3ffff07e387

def z428 : W := mkw 0x6b5d3004d22c838b 0x1395a2e0df2da383 0xffffffffff3fc7ef 0xdbffe3e1ffffe387

def z429 : W := mkw 0x9002040901424c60 0xc008581500105854 0x000f1e3fc7c03af3 0xe40cfc1e0018fc78

def z430 : W := mkw 0xb4a20e4b49d65ce1 0xc86add5da0d2dd76 0xf00f1fffc7fffefb 0xfc7cfc7f80f8ffff

def z431 : W := mkw 0xa945200452248095 0x139de8e69601a182 0x000fe0000701c081 0x038ce0660700e180

def z432 : W := mkw 0x94a20e4b09d25c60 0xc86a5d1d20d25c74 0x00001ff800c03850 0xa47c1c1e00f81c78

def z433 : W := mkw 0x926b569901736f6a 0xc2dc5bbf0db85afc 0x03fffff800fffbdb 0xa7fc1ffe0ff81ff8

def z434 : W := mkw 0x01868d2724000010 0x212b6c0002536c00 0x03f01fc7ffc00372 0xe073fc0008e7fc00

def z435 : W := mkw 0x7db42a46da9e93eb 0xd963b759fac7b767 0xfff01fc7fffe3f7e 0xf873ff99f8e7fe67

def z436 : W := mkw 0xb947240d5366cce1 0xd309f8f59611f9d6 0xf00ffe3fc7fffefb 0xff8cfc7f8718ffff

def z437 : W := mkw 0x74b20e4bc9de5f0b 0xc800020048d6df77 0x03ff1ffffffffc03 0xfc00000008ffffff

def z438 : W := mkw 0x2945200452248081 0x1301a0e09601a182 0xf00fe007c73fc6ab 0x5b80e0618700e387

def z439 : W := mkw 0x46f95ad288b9330a 0x0af607aa6dee06a9 0x0ffffff8383ffbcf 0x87ff03fe7fff03f8

def z440 : W := mkw 0xe9142004d20c80f5 0x112bfc55f205a103 0xfc000007ff000434 0x5803fc01f007e007

def z441 : W := mkw 0xb043040941664feb 0xc208daf58c10dbd6 0xf3fffe3fc7fffffb 0xff8cffff8f18ffff

def z442 : W := mkw 0xf4320649c9de5feb 0xc848db5de894db77 0xfc0f1e3fc7fffeff 0xfc0cfffff018ffff

def z443 : W := mkw 0x038e9d2724000014 0x23ff6daa337b6c00 0x0fffffffffc003f7 0xe3ffff807ffffc00

def z444 : W := mkw 0x0020429000112000 0x0040010a00800028 0x0000000000003800 0x0400001e00000078

def z445 : W := mkw 0x54b00a42889a136a 0xc840131968c61665 0xfff01fc7f8fe3c0e 0xf8000399f8e71e67

def z446 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xfff0e000383fc50c 0x1b8303e1ff070387

def z447 : W := mkw 0x0249509000212000 0x02d401aa05280088 0x000fe0380001c3c9 0x07fc03fe07180198

def z448 : W := mkw 0xf4b20e4bc9de5fff 0xcbfffffff8d6df77 0xffff1fffffffffff 0xfffffffff8ffffff

def z449 : W := mkw 0x0000000000000014 0x0123240030000000 0x0c00000000000004 0x0003000070000000

def z450 : W := mkw 0x54b00a42889a137e 0xcbf737bb78c61665 0xfff01fc7f8fe3f7e 0xfbf31f99f8e71e67

def z451 : W := mkw 0x8249509000212094 0x039de8e695280088 0x000fe0380001c081 0x078ce06607180198

def z452 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0x00000000000000d0 0x03fcfc7e00000000

def z453 : W := mkw 0x0002040100000000 0x0008480000104800 0x000f1e3fc7fffafb 0xe40cfc7e0018fff8

def z454 : W := mkw 0x004100000020038a 0x0301a2e09c000280 0xffffe000003fc3af 0x0383e3e1ff000380

def z455 : W := mkw 0x028a9d2324000000 0x20000000017a4c00 0x00001ff800c00000 0xa000000000f81c00

def z456 : W := mkw 0x60100000c00c038b 0x00008240c8048303 0xffff0007ff3fc7af 0x5803e3e1f807e387

def z457 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0x03fffff8003ff903 0x87f003800ff803f8

def z458 : W := mkw 0x038e9d2724000000 0x20084800037b6c00 0x03ffffffffc002f3 0xe00cfc000ffffc00

def z459 : W := mkw 0x68512000d22c838b 0x120082e0dc048383 0xfc0f0007c73fc6af 0x5800e3e1f000e387

def z460 : W := mkw 0x68716290d23da38b 0x124083eadc8483ab 0xfc000000003ffc0c 0x1c0003fff00003ff

def z461 : W := mkw 0x2b4d70945225a081 0x1395a0e29729a18a 0x000fe0380701c081 0x078ce0660718e198

def z462 : W := mkw 0x80000000000000f4 0x032bfcf5b0000000 0xfc000000000003bc 0x0383ffe1f0000000

def z463 : W := mkw 0x038e9d2724000010 0x23ff6daa037b6c00 0x03ffffffffc003fb 0xe3fffffe0ffffc00

def z464 : W := mkw 0x547142d088bb336a 0xca4013bb6c8412ed 0xfc000000003ffc0c 0x1c0003fff00003ff

def z465 : W := mkw 0x0000000000000000 0x0000000000000000 0x000f00380001c081 0x040c006600180198

def z466 : W := mkw 0x2945200452248001 0x100000000601a182 0x000fe0000701c001 0x000000000700e180

def z467 : W := mkw 0x030e952524000000 0x2000000003396800 0x000fe03807000001 0x000000000718e000

def z468 : W := mkw 0x0104000400000080 0x0301a0e092012000 0xffffe007ff0003af 0x4383e3e1ff07e000

def z469 : W := mkw 0x69552004d22c830b 0x100002004e05a383 0xffffe007ff3fc72f 0x58030381ff07e387

def z470 : W := mkw 0xb20a140941464ce1 0xc09cd8558138d956 0xf3ffffffc7fffffb 0xfffcfc7f8ff8ffff

def z471 : W := mkw 0x0249509000212000 0x0000000005280088 0x000fe0380001c001 0x0400000007180198

def z472 : W := mkw 0x1480084208821060 0xc822141120421444 0x0000000000c00010 0x20001c0000001c00

def z473 : W := mkw 0x69552004d22c838b 0x1101a240de05a383 0xffffe007ff3fc427 0x5803e001ff07e387

def z474 : W := mkw 0x0000000000000000 0x024001aa00000000 0x0000000000000008 0x000003fe00000000

def z475 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0x03ffe1f80001c181 0x07fc03e60ff80198

def z476 : W := mkw 0x0000000000000094 0x03f7a5eab0000000 0xfc000000000003ac 0x03f3e3e1f0000000

def z477 : W := mkw 0x0000000000000000 0x029400a200000000 0x0000000000000080 0x038c006600000000

def z478 : W := mkw 0x826952900031239e 0x03ddebee9da802a8 0x03fffff8003ffbcb 0x87fce3fe0ff803f8

def z479 : W := mkw 0x0249509000212000 0x029400a205280088 0x0000e00000000000 0x0380000007000000

def z480 : W := mkw 0x9002040901424cf4 0xc3fffdffb0105854 0xfc001e3800c03bfc 0xa7fffffff0181c78

def z481 : W := mkw 0x0002040100000000 0x0008480000104800 0x00000007c7c00030 0x6000fc000000fc00

def z482 : W := mkw 0x47bc9b66ac98131a 0x29f727086bef2621 0x0ff0e1c038000104 0x03f303807fe70000

def z483 : W := mkw 0xe9552004d22c83eb 0x1309faf5de05a383 0xffffe007ff3fc7ff 0x5b8fffffff07e387

def z484 : W := mkw 0x026952900031231e 0x03f727aa3da802a8 0x0ffffff8003ffbcf 0x87ff03fe7ff803f8

def z485 : W := mkw 0x14a00a4208921060 0xc862151920c21464 0x03f01fc7f8c03b72 0xe0731c1808e71c60

def z486 : W := mkw 0x038e9d2724000010 0x212b6c00037b6c00 0x03ffffffffc00033 0xe003fc000ffffc00

def z487 : W := mkw 0x014500040020030a 0x030122a00e012280 0x03ffe007ff3fc3ab 0x4383e3e00f07e380

def z488 : W := mkw 0x922a569901536c60 0xc0dc591f01b8587c 0x00001ff800c03850 0xa47c1c1e00f81c78

def z489 : W := mkw 0x6df52a46dabc938b 0x1b63a7e8fec7a7a3 0xffffe1c7ff3fc7af 0x5bf3e3e1ffe7e387

def z490 : W := mkw 0xb002040941464cf5 0xc0fedd5fa010d956 0xf00f1e3fc7fffefb 0xfc7cfc7f8018ffff

def z491 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0xf0000007c7fffc38 0x7c00fc7f8000ffff

def z492 : W := mkw 0xb002040941464ce1 0xc2dcd9ff8010d956 0xf00f1e3fc7fffffb 0xfffcffff8018ffff

def z493 : W := mkw 0x8000000000000094 0x0109e84490000000 0x0000000000000000 0x0000e00000000000

def z494 : W := mkw 0xe8512000d22c83ff 0x13fffffffc048383 0xfc000000003fc7fc 0x1bfffffff0000387

def z495 : W := mkw 0x006142900031230a 0x024003aa0c8002a8 0x000f1e38003ffacb 0x840c03fe001803f8

def z496 : W := mkw 0xa002040941444c81 0x0008c8448010c912 0xf00f003fc73fc6ab 0x5c0ce0678018e39f

def z497 : W := mkw 0x004100000020030a 0x020002a00c000280 0x00000000003fc008 0x000003e000000380

def z498 : W := mkw 0x80000000000000f4 0x02feddffb0000000 0xfc0000000000005c 0x007c1ffff0000000

def z499 : W := mkw 0x022852900011230a 0x00d4030a09a80228 0x03f01ff8003e3b4a 0x847c039e08f80278

def z500 : W := mkw 0x838e9d2724000094 0x23bfece6937b6c00 0x03ffffffffc003f3 0xe3fffc660ffffc00

def z501 : W := mkw 0xb000000841464ce1 0xc000905580009156 0xf00f1e38003ffecb 0x9c0c007f801803ff

def z502 : W := mkw 0x50100000800a036a 0xc000121148041245 0xfff01e07f8fe3f7e 0xf8031f99f8071e67

def z503 : W := mkw 0x338e9d2f65464c11 0xe1bf6c00037bfd56 0x03fffffffffffff3 0xfffffc000fffffff

def z504 : W := mkw 0x0208100000000000 0x0094000001280000 0x00001ff800000040 0x807c000000f80000

def z505 : W := mkw 0x69552004d22c839b 0x13bfeee0de05a383 0xffffe007ff3fc7ff 0x5bffffe1ff07e387

def z506 : W := mkw 0x2104000440040081 0x0101a0408201a102 0xf3ffe007ff3fc7ab 0x5b83e0618f07e387

def z507 : W := mkw 0x0000000000000060 0x0022141120000000 0xfc00000000000034 0x00031c01f0000000

def z508 : W := mkw 0xe957240dd36ccf8b 0x1309eae4de15eb93 0xffffe03fff3fc7af 0x5f8fe3e7ff1fe39f

def z509 : W := mkw 0x54b00a42889a13ea 0xcb63b7f9f8c61665 0xfff01fc7f8fe3ffe 0xfbf3fff9f8e71e67

def z510 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x03fffffffffffbfb 0xe7fffc7e0ffffff8

def z511 : W := mkw 0x826952900031237e 0x02fe5fbf2da802a8 0x03fffff8003ffbdb 0x87fc1ffe0ff803f8

def z512 : W := mkw 0x8000000000000094 0x03bfece690000000 0x00000000000003f0 0x03fffc6600000000

def z513 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0x00001ff8003ff848 0x847c03fe00f803f8

def z514 : W := mkw 0x138e9d2724020070 0xe1bf7c11037b7c44 0xf3fffffffffe3ffb 0xfbfffc198ffffe67

def z515 : W := mkw 0x03efdfb72431231a 0x23ff6faa0ffb6ea8 0x03ffffffffc003f3 0xe3ffff800ffffc00

def z516 : W := mkw 0x80020401000000f4 0x03fffdffb0104800 0xfc0f1e3fc7c003ff 0xe3fffffff018fc00

def z517 : W := mkw 0xb106040d41464ce1 0xc109f8558211f956 0xf3fffe3ffffffffb 0xff8ffc7f8f1fffff

def z518 : W := mkw 0x4010000080080000 0x0000000040040001 0xfc000007f8000424 0x58030001f0070007

def z519 : W := mkw 0x54b00a42889a136a 0xcaf617bb68c61665 0xfff01fc7f8fe3ffe 0xfbff1ffff8e71e67

def z520 : W := mkw 0x326b569941776f0b 0xc00002000db8dbfe 0x03ffffffc7fffc03 0xfc0000000ff8ffff

def z521 : W := mkw 0x80000000000000e4 0x00009055b0000000 0xfc00000000000004 0x00000001f0000000

def z522 : W := mkw 0x0228529000112000 0x02d401aa01a80028 0x00001ff800003bc8 0x87fc03fe00f80078

def z523 : W := mkw 0x2000000040040081 0x0000804080008102 0xf00f1e3fc73ffeeb 0xdc0ce07f8018e3ff

def z524 : W := mkw 0x56f95ad288bb330a 0xcad403aa4dee16ed 0x03fffffff8ffffcb 0xfffc03fe0fff1fff

def z525 : W := mkw 0x5df52a469aba936a 0xdb6337b97ec736e5 0xfff0ffc7f8fe3f7e 0xfbf31f99ffe71e67

def z526 : W := mkw 0x405100008028030a 0x020002a04c040281 0xffffe007f83fc7af 0x5b8303e1ff070387

def z527 : W := mkw 0x026952900031236a 0x02f617bb2da802a8 0xfffffff8003ffbff 0x87ff1ffffff803f8

def z528 : W := mkw 0x80000000000000e0 0x0000905580000000 0xf000000000000008 0x0000007f80000000

def z529 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x03f0fff838c00150 0xa3ff1c000fff1c00

def z530 : W := mkw 0x006142900031230a 0x024003aa0c8002a8 0x0000000000000000 0x0000038000000000

def z531 : W := mkw 0xb24b549941676ce1 0xc29cd8f78538d9de 0xf00ffe3fc7fffefb 0xff8cfc7f8718ffff

def z532 : W := mkw 0x3002040941464c01 0xc00000000010d956 0x000f1e3fc7fffecb 0xfc0c007e0018ffff

def z533 : W := mkw 0x102002000012036a 0xc040131908801264 0xf3f01fc7c0fe3f7a 0xf8701f9988e01e67

def z534 : W := mkw 0x2945200452248081 0x1301a0e09601a182 0x03ffe007ff01c3a3 0x4383e0600f07e180

def z535 : W := mkw 0xb269529841776feb 0xc2d493ff8da893fe 0xf3fffff8003fffcb 0x9ffc03ff8ff803ff

def z536 : W := mkw 0x0080080200000010 0x01bf6c0000420400 0x03f01fc7f8c003f2 0xe3fffc0008e71c00

def z537 : W := mkw 0x238e9d2764040091 0x21bfec40837bed02 0xf3ffffffffffc7fb 0xfbfffc618fffff87

def z538 : W := mkw 0x68512000d22c838b 0x1301a2e0dc048383 0xfc000000003fc7ac 0x1b83e3e1f0000387

def z539 : W := mkw 0x54300240889a136a 0xc840131968841265 0xfff00007f83e3f2e 0x58030399f8070267

def z540 : W := mkw 0x44b00a428898130a 0x0862070868c60621 0xfff001c7f83e072e 0x58730381f8e70207

def z541 : W := mkw 0x036d52940031230a 0x03d523aa0fa922a8 0x03ffffffff3ffbeb 0xc7ffe3fe0fffe3f8

def z542 : W := mkw 0x0000000000000000 0x0000000000000000 0x03f01fc000000342 0x8070000008e00000

def z543 : W := mkw 0xb002040941464c81 0xc008c8448010d956 0x000f1e3fc7fffc83 0xfc0ce0660018ffff

def z544 : W := mkw 0x80000000000000e0 0x006add5da0000000 0xfc000000000003fc 0x007ffffff0000000

def z545 : W := mkw 0x6b7d7294d23da30b 0x100002004fada3ab 0x03ffffffff3ffc03 0xdc0000000fffe3ff

def z546 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0xf00f0007c7ffc6bb 0x7800fc618000ff87

def z547 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0xf0001e3800fffc58 0xbc0c1c7f80181fff

def z548 : W := mkw 0x80000000000000f4 0x03bffcf7b0000000 0xfc000000000000b4 0x038ffc67f0000000

def z549 : W := mkw 0x002002000010036a 0x0062171928800220 0xfff01fc0003e3b7e 0x80731f99f8e00260

def z550 : W := mkw 0x006142900031230a 0x024003aa0c8002a8 0x03f01fc0003ffb4a 0x847003fe08e003f8

def z551 : W := mkw 0x0249509000212000 0x029400a205280088 0x03fffff80001c3c3 0x87fc00660ff80198

def z552 : W := mkw 0x026952900031230a 0x024003aa0da802a8 0x03fffff8003ff80b 0x840003fe0ff803f8

def z553 : W := mkw 0x0000000000000080 0x03d5a1ea90000000 0xfc000000000003ec 0x03ffe3fff0000000

def z554 : W := mkw 0x02e95a920031230a 0x02f607aa0dea06a8 0x03fffffff8fffbfb 0xe7ff1ffe0fff1ff8

def z555 : W := mkw 0x0080080200000000 0x0022040000420400 0x03f001c038000100 0x0073000008e70000

def z556 : W := mkw 0x0080080200000060 0x0062151920420400 0xfff01fc7f8c0037e 0xe0731f99f8e71c00

def z557 : W := mkw 0x3002040941464c81 0xc00080408010d956 0xf00f1e3fc7fffeab 0xfc00e0618018ffff

def z558 : W := mkw 0x54100040888a1060 0xc800101160041045 0xfc00000000000404 0x18000001f0000007

def z559 : W := mkw 0x74b00a42c89e13eb 0xc8629759e8c69767 0xffff1fc7ffffffff 0xf873fff9f8e7ffe7

def z560 : W := mkw 0xebdfbd27f62c83ff 0x33ffffffff7fef83 0xffffffffffffc7ff 0xfbffffffffffff87

def z561 : W := mkw 0x54300240889a136a 0xc840131968841265 0xfc001e07c0fe3e7e 0xf8001f99f0001e67

def z562 : W := mkw 0x2000000040040081 0x0000804080008102 0x000f00000701c081 0x0000e0600000e180

def z563 : W := mkw 0x495520049228838a 0x1301a2e0de052281 0xfff0e000380003ac 0x0383e3e1ff070000

def z564 : W := mkw 0x030c912424000010 0x2195200003292000 0x0000e00000000000 0x0380000007000000

def z565 : W := mkw 0x8000000000000074 0x01ff7d1f20000000 0x00000000000003f0 0x03fffc1e00000000

def z566 : W := mkw 0x004100000020030a 0x020002a00c000280 0x03fffe38003ffbcb 0x878c03fe0f1803f8

def z567 : W := mkw 0x82695290003123ea 0x02dcdbff8da802a8 0xf3fffff8003ffbfb 0x87fcffff8ff803f8

def z568 : W := mkw 0x0208100000000010 0x01bf6c0001280000 0x03fffff8000003f3 0x83fffc000ff80000

def z569 : W := mkw 0x55b40a46889a136a 0xc96337196ac73665 0xffffffc7fffe3fff 0xfbf3ff99ffe7fe67

def z570 : W := mkw 0x6a797290d23da38b 0x12d483eaddac83ab 0xfffffff8003fffcf 0x9ffc03fffff803ff

def z571 : W := mkw 0x338e9d2f65464c01 0xe0000000037bfd56 0x03fffffffffffc03 0xfc0000000fffffff

def z572 : W := mkw 0x03aedfb724112010 0x21ff6d0a03fb6c28 0x03ffffffffc03bf3 0xe7fffc1e0ffffc78

def z573 : W := mkw 0x8228529000112074 0x00fe5d1f21a80028 0x00001ff800003850 0x847c1c1e00f80078

def z574 : W := mkw 0x56ba9f63ac9a137a 0xe8fe5f1969fe5e65 0xfff01ffff8fe3f7e 0xf87f1f99f8ff1e67

def z575 : W := mkw 0xb002040941464cf5 0xc12bfc55b010d956 0xfc0f1e3fc7fffeff 0xfc0ffc7ff018ffff

def z576 : W := mkw 0x2841200052248081 0x120080e094008182 0x000000000001c000 0x0000006000000180

def z577 : W := mkw 0x81868d27240000f4 0x212bfc55b2536c00 0xfc000007ffc00034 0x6003fc01f007fc00

def z578 : W := mkw 0x838e9d27240000f0 0x21bffc55837b6c00 0xf3ffffffffc003fb 0xe3fffc7f8ffffc00

def z579 : W := mkw 0x3002040941464c61 0xc00010110010d956 0xf00f1e3fc7fffe7b 0xfc001c198018ffff

def z580 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xfc000007f8fe3c3c 0x78031f99f0071e67

def z581 : W := mkw 0x54b00a42889a130a 0xc840030848c61665 0x03f01fc7f8fe3f4a 0xf870039808e71e67

def z582 : W := mkw 0x00820c0300000000 0x002a4c0000524c00 0x03ff1fffffc003f3 0xe07ffc0008fffc00

def z583 : W := mkw 0x54300240889a136a 0xc840131968841265 0xfff01fc0003e3f4e 0x98700399f8e00267

def z584 : W := mkw 0xf8512008d36ecfeb 0xd20092f5dc0493d7 0xfc000000003ffc0c 0x1c0003fff00003ff

def z585 : W := mkw 0x00a00a020010030a 0x0062070808c20620 0x03f01fc7f8fe3b7a 0xe0731f9808e71e60

def z586 : W := mkw 0x034fd5b524212010 0x239d68a207396888 0x000fe0380701c081 0x078ce0660718e198

def z587 : W := mkw 0x00828d2324000010 0x202a4c0000524c00 0x0000000000c00010 0x20001c0000001c00

def z588 : W := mkw 0x004100000020030a 0x020002a00c000280 0x03f0e00000000100 0x038003800f000000

def z589 : W := mkw 0x56b85ad2889b336a 0xc8f6171b69ee166d 0xfff01ffff8fe3f7e 0xfc7f1f9ff8ff1e7f

def z590 : W := mkw 0xa002040941444c81 0x0008c8448010c912 0x0000000007000000 0x0000e0000000e000

def z591 : W := mkw 0x8000000000000074 0x00fe5d1f20000000 0xfc0000000000037c 0x007f1f9ff0000000

def z592 : W := mkw 0xf7be9f6fedde5ffb 0xe9ffff5debffff77 0xffffffffffffffff 0xffffffffffffffff

def z593 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0xf0001e07c7fe3e7a 0xf800fc198000fe67

def z594 : W := mkw 0x0000000000000000 0x0000000000000000 0x000f0000003fc28b 0x0000006000000380

def z595 : W := mkw 0x80000000000000f4 0x012bfc55b0000000 0xfc000000000002fc 0x000ffc7ff0000000

def z596 : W := mkw 0x579e9d67ac8a1070 0xe9bf7c11637f7c45 0xffffffffffc007f7 0xfbfffc01fffffc07

def z597 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0xf00f003fc7c1c4b1 0x7c0cfc678018fd9f

def z598 : W := mkw 0x0000000000000000 0x0000000000000000 0x000f1e38003ff803 0x84000000001803f8

def z599 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0x03ffe1c0003fc38b 0x03f003e00fe00380

def z600 : W := mkw 0x69142004d20c8081 0x1301a0e0d205a103 0xfc000007ff0007ac 0x5b83e3e1f007e007

def z601 : W := mkw 0xb000000841464ce1 0xc000905580009156 0xf00f0007c73ffeab 0x5c00e07f8000e3ff

def z602 : W := mkw 0x2000000040040001 0x0000000000008102 0x000f0007c73fc403 0x580000000000e387

def z603 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001e07c0c00272 0xe0001c0000001c00

def z604 : W := mkw 0xb002040941464cf1 0xc1bffc558010d956 0xf00f1e3fc7fffffb 0xfffffc7f8018ffff

def z605 : W := mkw 0x4df52a469ab8930a 0x1b6327a87ec726a1 0x0ff0e1c038000104 0x03f303807fe70000

def z606 : W := mkw 0x03eddbb62431231a 0x23f727aa0feb26a8 0x03f0e1c038000100 0x03f303800fe70000

def z607 : W := mkw 0xc9552004922883fe 0x13fffffffe052281 0xfff0e000380003fc 0x03ffffffff070000

def z608 : W := mkw 0x44b00a428898136a 0x0862171968c60621 0xfff001c03800037c 0x00731f99f8e70000

def z609 : W := mkw 0x54b00a42889a1060 0xc862151960c61465 0xfc001fc7f8c03c74 0xf8731c19f0e71c67

def z610 : W := mkw 0x0080080200000000 0x0022040000420400 0x00000007f8c00030 0x60031c0000071c00

def z611 : W := mkw 0x022812000010030a 0x00d4030809a80220 0x03fffff8003e3bcb 0x83fc03980ff80260

def z612 : W := mkw 0xa002040941444c81 0x0008c8448010c912 0x000f1e3fc7c1c2f3 0xe40cfc660018fd98

def z613 : W := mkw 0xe9552004d22c83ff 0x132bfef5fe05a383 0xffffe007ff3fc7bf 0x5b83ffe1ff07e387

def z614 : W := mkw 0x74b20e4bc9de5f6b 0xc862171968d6df77 0xffff1fffffffff7f 0xfc731f99f8ffffff

def z615 : W := mkw 0x55968d67ac8a1070 0xe92b7c1162577c45 0xfc000007ffc00434 0x7803fc01f007fc07

def z616 : W := mkw 0x0002040100000000 0x0000000000104800 0x000f1e3fc7c00003 0xe00000000018fc00

def z617 : W := mkw 0x8002040901404c00 0x0008480400104810 0x0000003800000000 0x040c000600180018

def z618 : W := mkw 0x54b00a42889a130a 0xc800020048c61665 0xfff01fc7f8fe3f2e 0xf8030381f8e71e67

def z619 : W := mkw 0x8000000000000080 0x0008c84480000000 0x0000000000000080 0x000ce06600000000

def z620 : W := mkw 0x80200200001003fe 0x03ffffffb8800220 0xfff01fc0003e3bfe 0x83fffffff8e00260

def z621 : W := mkw 0x567952d088bb336a 0xcad413bb6dac12ed 0xfffffff8003fffcf 0x9ffc03fffff803ff

def z622 : W := mkw 0x57be9f67ac9a136a 0xe86217196bff7e65 0xfffffffffffe3f7f 0xf8731f99fffffe67

def z623 : W := mkw 0x9002040901424c60 0xc008581500105854 0xf0001e3fc0fe3e7a 0xfc0c1c1f80181e7f

def z624 : W := mkw 0x54b00a42889a136a 0xc822161168c61665 0xfff01fc7f8fe3c36 0xf8031c01f8e71e67

def z625 : W := mkw 0x1000000000020060 0xc000101100001044 0x00001e0000c03850 0xa0001c1800001c60

def z626 : W := mkw 0x94a00a4208921074 0xc8fe5d1f20c21464 0x00001fc000c03850 0xa07c1c1e00e01c60

def z627 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0xf00f0038073ffc89 0x1c0ce07f8018e3ff

def z628 : W := mkw 0x411400048008030a 0x010122004a052201 0xffffe007ff3e07af 0x5b83e381ff07e207

def z629 : W := mkw 0x4490084288881000 0x0822040060460401 0x0c00000038000004 0x0003000070070000

def z630 : W := mkw 0x4b7d72949239a30a 0x13d523aa5fad22a9 0x0ff0e1c038000104 0x03f303807fe70000

def z631 : W := mkw 0x1000000000020060 0xc000101100001044 0xf00f1e3fc0fffefb 0xfc0c1c7f80181fff

def z632 : W := mkw 0x2b6d72945235a38b 0x13d5a3ea9fa9a3aa 0x03fffff8073ffbcb 0x87fce3fe0ff8e3f8

def z633 : W := mkw 0x0106852524000010 0x2109680002116800 0x0000000007000000 0x0000e0000000e000

def z634 : W := mkw 0xb061429841776feb 0xc24093ff8c8093fe 0xf0000000003ffc08 0x1c0003ff800003ff

def z635 : W := mkw 0x004100000020030a 0x02d403aa0c000280 0x03ffe000003fc3cb 0x03fc03fe0f000380

def z636 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0xf0001e3fc7c03c70 0xfc0cfc1f8018fc7f

def z637 : W := mkw 0x038c992624000010 0x21b72400036b2400 0x03f0ffc7f8c00372 0xe3f31c000fe71c00

def z638 : W := mkw 0x026952900031231a 0x03ff6faa0da802a8 0x03fffff8003ffbfb 0x87fffffe0ff803f8

def z639 : W := mkw 0x17ae9f672c921070 0xe9ff7d1923fb7c64 0x03ffffffffc03bf3 0xe3fffc180ffffc60

def z640 : W := mkw 0x14a00a420892136a 0xc862171928c21664 0x03f01fc000fe3b5a 0xa0701f9808e01e60

def z641 : W := mkw 0x03efdfb72431230a 0x22d403aa0ffb6ea8 0x03fffffffffffbcb 0xe7fc03fe0ffffff8

def z642 : W := mkw 0xa002040941444c81 0x0008c8448010c912 0x000f1e38073ffacb 0x840ce07e0018e3f8

def z643 : W := mkw 0x0104000400000000 0x0101200002012000 0x03f0e00038000100 0x038300000f070000

def z644 : W := mkw 0x495520049228830a 0x130122a05e052281 0xfff0e007f83e072e 0x5b830381ff070207

def z645 : W := mkw 0x006102000030030a 0x024003a80c8002a0 0x03ffffc0003ffbcb 0x83f003f80fe003e0

def z646 : W := mkw 0x69552004d22c830b 0x130122a05e05a383 0x0fffe007ff3fc507 0x5b8303807f07e387

def z647 : W := mkw 0x838e9d2724000074 0x21ff7d1f237b6c00 0x03ffffffffc003f3 0xe3fffc1e0ffffc00

def z648 : W := mkw 0x54b20e43889a136a 0xc86a5f1968d65e65 0xffff1ffffffe3fff 0xf87fff99f8fffe67

def z649 : W := mkw 0x439e9d27a408031a 0x21bf6e004b7f6e01 0xfffffffffffe07ff 0xfbffff81fffffe07

def z650 : W := mkw 0x55b68f67ac9a137a 0xe96b7f196ad77e65 0xfff01fc7fffe3f7e 0xf873ff99f8e7fe67

def z651 : W := mkw 0x1420024008921060 0xc840111920801064 0x0000000000003800 0x0000001800000060

def z652 : W := mkw 0x04a00a4208901000 0x0862050820c20420 0x000001c000000000 0x0070000000e00000

def z653 : W := mkw 0x01868d2724000000 0x2000000002536c00 0x00000007ffc00000 0x600000000007fc00

def z654 : W := mkw 0x0104000400000000 0x0101200002012000 0x00000007ff000020 0x4003e0000007e000

def z655 : W := mkw 0x9002040901424c60 0xc008581500105854 0x0000000000c00010 0x20001c0000001c00

def z656 : W := mkw 0x0208509000012000 0x0094000201280008 0x0000003800000000 0x040c000600180018

def z657 : W := mkw 0x44b00a428898131e 0x0bf727aa78c60621 0x0ff001c038000104 0x03f3038078e70000

def z658 : W := mkw 0x03cf9d272420031a 0x23bf6ea00f7b6e80 0x03ffffffffffc3fb 0xe3ffffe00fffff80

def z659 : W := mkw 0x401000008008030a 0x0000020048040201 0xfc000000003e040c 0x18000381f0000207

def z660 : W := mkw 0x838e9d27240000f4 0x21bffc55b37b6c00 0xffffffffffc003f7 0xe3fffc01fffffc00

def z661 : W := mkw 0x69142004d20c8081 0x1101a040d205a103 0xffffe007ff0007a7 0x5b83e001ff07e007

def z662 : W := mkw 0x0228529000112000 0x0000000001a80028 0x00001ff800003800 0x8400000000f80078

def z663 : W := mkw 0x2904200452048081 0x1101a0409201a102 0x0000000007000000 0x0000e0000000e000

def z664 : W := mkw 0x01868d2724000010 0x21bf6c0002536c00 0x00000007ffc003f0 0x63fffc000007fc00

def z665 : W := mkw 0x928a9d2b25424c70 0xe0be5c15017a5c54 0x00001ff800c03850 0xa47c1c1e00f81c78

def z666 : W := mkw 0x69552004d22c83eb 0x1363b7f9fe05a383 0xffffe007ff3fc7ff 0x5bf3fff9ff07e387

def z667 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0x0fffe0003f01c185 0x0383e3e07f07e180

def z668 : W := mkw 0x0106040500000000 0x0109680002116800 0x03fffe3fffc003f3 0xe38ffc000f1ffc00

def z669 : W := mkw 0x028a9d2324000010 0x20be4c00017a4c00 0x000f1fffc7c002f3 0xe07cfc0000f8fc00

def z670 : W := mkw 0xb0820c0b41464ce1 0xc02adc558052dd56 0xf3ff1ffffffffffb 0xfc7ffc7f88ffffff

def z671 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0xf00f1e3fc7c006f3 0xf80cfc018018fc07

def z672 : W := mkw 0x294520045224838b 0x1301a2e09e01a382 0x03ffe000073fc38b 0x0380e3e00f00e380

def z673 : W := mkw 0xfdf52a46dabe93ff 0xdbfffffffec7b7e7 0xffffffc7ffffffff 0xfbffffffffe7ffe7

def z674 : W := mkw 0x80410000002003fe 0x03ffffffbc000280 0xffffe000003fc3ff 0x03ffffffff000380

def z675 : W := mkw 0x403002008018030a 0x0040030848840221 0xfff01fc7f83e3f6e 0xd8730399f8e70267

def z676 : W := mkw 0x0002040100000000 0x0008480000104800 0x00001e3800c00050 0xa00c1c0000181c00

def z677 : W := mkw 0xf916240dd34ecce1 0xd109f855d215f957 0xfc0f1e3ffffffeff 0xfc0ffc7ff01fffff

def z678 : W := mkw 0x030c100400000000 0x0195200003292000 0x03ffffffff0003e3 0xc3ffe0000fffe000

def z679 : W := mkw 0x8000000000000014 0x009c480600000000 0x0000000000000000 0x000c000600000000

def z680 : W := mkw 0x2bcfbd2776248091 0x33bfece0977bed82 0x03ffffffffc1c3f3 0xe3fffc600ffffd80

def z681 : W := mkw 0xd4b20e4b89da5f6a 0xc86a5f1d68d65e75 0xfff01ffff8fe3f7e 0xfc7f1f9ff8ff1e7f

def z682 : W := mkw 0xf0120409c14e4feb 0xc008da55c814db57 0xffff1e3fffffffff 0xfc0ffffff81fffff

def z683 : W := mkw 0x020a952124000010 0x209c480001384800 0x0000003800000000 0x000c000000180000

def z684 : W := mkw 0x485120009228830a 0x120002a05c040281 0x0c00000000000004 0x0000038070000000

def z685 : W := mkw 0x0000000000000010 0x03ff6daa00000000 0x00000000000003f8 0x03fffffe00000000

def z686 : W := mkw 0xb30e952d65464cf1 0xe19df8558339f956 0xf00ffe3fc7fffefb 0xff8cfc7f8718ffff

def z687 : W := mkw 0x0288180200000000 0x00b60400016a0400 0x03fffffff8c003f3 0xe3ff1c000fff1c00

def z688 : W := mkw 0xd4900842888a10f4 0xcbfffdfff0461445 0xfc000007f8c007fc 0x7bfffffff0071c07

def z689 : W := mkw 0x0041409000212000 0x020000a204000088 0x000000000001c000 0x0400006600000198

def z690 : W := mkw 0x69552004d22c830b 0x120002a04e05a383 0x03ffe007ff3fc78b 0x5b8003e00f07e387

def z691 : W := mkw 0x038e9d2724000010 0x21b72400037b6c00 0x03ffffffffc00103 0xe3f300000ffffc00

def z692 : W := mkw 0x54f10a4288ba136a 0xca6217b96cc616e5 0xffffffc7f8ffffff 0xfbf31ff9ffe71fe7

def z693 : W := mkw 0x01868d2724000010 0x212b6c0002536c00 0x03ffe007ffc003b3 0x6383fc000f07fc00

def z694 : W := mkw 0x0104000400000000 0x0101200002012000 0x000fe00007000081 0x0380e0000700e000

def z695 : W := mkw 0x7fffbf67febe93fb 0xfbfffff9ffffffe7 0xffffffffffffffff 0xfbfffff9ffffffe7

def z696 : W := mkw 0x6bffffb7f63da39b 0x33ffefeadfffefab 0xffffffffffffffff 0xffffffffffffffff

def z697 : W := mkw 0x79552004d22e83eb 0xd301b2f1de05b3c7 0xfffffe07ffffffff 0xfb83fff9ff07ffe7

def z698 : W := mkw 0x8000000000000074 0x02fe5dbf20000000 0x00000000000003d8 0x03fc1ffe00000000

def z699 : W := mkw 0x80000000000000e0 0x02dcd9ff80000000 0xf0000000000003f8 0x03fcffff80000000

def z700 : W := mkw 0x9000000801424c60 0xc000101500001054 0x0000000000003800 0x0400001e00000078

def z701 : W := mkw 0x0000000000000010 0x012b6c0000000000 0x0000000000000030 0x0003fc0000000000

def z702 : W := mkw 0x0000000000000010 0x019d680000000000 0x0000000000000080 0x038ce00000000000

def z703 : W := mkw 0x026b56910031230a 0x02dc4baa0db84aa8 0x03ffffffc7fffbfb 0xe7fcfffe0ff8fff8

def z704 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001e3800003840 0x840c001e00180078

def z705 : W := mkw 0xb38e9d2f65464cf1 0xe1bffc55837bfd56 0xf3ffffffffc007f3 0xfbfffc018ffffc07

def z706 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0x03f0e1c0000003c8 0x03fc03fe0fe00000

def z707 : W := mkw 0x0000000000000060 0x0062151920000000 0xfc0000000000003c 0x00031f99f0000000

def z708 : W := mkw 0x54f14ad288bb330a 0xc80002004cc616ed 0x03f01fc7f8fffc02 0xfc00000008e71fff

def z709 : W := mkw 0x69d7ad27f62c831b 0x312b6e004e57ef83 0x03ffe007ffffc433 0x7803fc000f07ff87

def z710 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x03ffffffffc00133 0xe3f3fc000ffffc00

def z711 : W := mkw 0x80000000000000f4 0x03f7b5ffb0000000 0xfc000000000003ac 0x03f3e3fff0000000

def z712 : W := mkw 0x838e9d2724000074 0x23ff7dbf337b6c00 0x0ff0fff838c00154 0xa3ff1f9e7fff1c00

def z713 : W := mkw 0x56f95ad288bb336a 0xc80012114dee16ed 0xf3fffffff8fffefb 0xfc0c1c7f8fff1fff

def z714 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0xf3fffffffffe07fb 0xfbfffc018ffffe07

def z715 : W := mkw 0x6b5fb525f62c830b 0x300002004f3deb83 0x03ffe03fff3fc403 0x580000000f1fe387

def z716 : W := mkw 0x2945200452248081 0x1301a0e09601a182 0xffffe007ff01c3af 0x4383e3e1ff07e180

def z717 : W := mkw 0x4a7972909239a30a 0x12d403aa5dac02a9 0x0ffffff8003ffbcf 0x87fc03fe7ff803f8

def z718 : W := mkw 0x0184080600000010 0x01bf6c0002432400 0x03ffffc7ffc003f3 0xe3fffc000fe7fc00

def z719 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0x03fffff8003ff8c3 0x87fc007e0ff803f8

def z720 : W := mkw 0x038c992624000014 0x23f725aa336b2400 0x0ffffff8380003cf 0x83ff03fe7fff0000

def z721 : W := mkw 0x7df52a46dabe93eb 0xd8009251cec7b7e7 0xf3ffffc7fffffefb 0xf800fc798fe7ffe7

def z722 : W := mkw 0x0000000000000080 0x0000804080000000 0xfc000000000003ac 0x0003e3e1f0000000

def z723 : W := mkw 0x54b00a42889a136a 0xc822161168c61665 0x03f01fc7f8fe3c12 0xf8001c0008e71e67

def z724 : W := mkw 0x0000000000000060 0x0062151920000000 0xfff00007f800037e 0x40731f99f8070000

def z725 : W := mkw 0x2945200452248081 0x1301a0e09601a182 0xfc0fe0000701c08d 0x0380e3e1f700e180

def z726 : W := mkw 0x8000000000000084 0x024081eeb0000000 0x0c00000000000004 0x000003e670000000

def z727 : W := mkw 0x82695290003120f4 0x03fffdffb5a800a8 0xfc0ffff80001fbfd 0x87fffffff7f801f8

def z728 : W := mkw 0x90020401000200f4 0xc3fffdffb0105844 0xfc0f1e3fc7fe3fff 0xfbfffffff018fe67

def z729 : W := mkw 0x0288992224000014 0x23f725aa316a0400 0x0c0001c000000104 0x03f3038070e00000

def z730 : W := mkw 0x7c712240dabe930b 0xd80002004c8493e7 0x00000000003ffc00 0x18000000000003e7

def z731 : W := mkw 0x3002040941464c15 0xc3f725aa3010d956 0x0c0f1e3fc7fffd07 0xfff303807018ffff

def z732 : W := mkw 0x838e9d27240000f4 0x23fffdffb37b6c00 0xffffffffffc003f7 0xe3ffff81fffffc00

def z733 : W := mkw 0x44b00a428898130a 0x0800020048c60621 0x03f01fc0383e3802 0x8000000008e70260

def z734 : W := mkw 0x90000000000200e4 0xc24091ffb0001044 0xfc001e07c0fe3e7e 0xf8001ffff0001e67

def z735 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc000000000001b4 0x03ffffe7f0000000

def z736 : W := mkw 0x0000000000000060 0x0040111920000000 0xfc0000000000032c 0x00030399f0000000

def z737 : W := mkw 0x54b20e43889a130a 0xc8084a0048d65e65 0x03ff1ffffffe3ef3 0xf80cfc0008fffe67

def z738 : W := mkw 0xb000000841464ce1 0xc062955da0009156 0xfc000000003fff7c 0x1c731ffff00003ff

def z739 : W := mkw 0xe9552004d22c837f 0x10fe5f1f6e05a383 0x03ffe007ff3fc453 0x587c1c1e0f07e387

def z740 : W := mkw 0xb002040941464cf5 0xc16bfd5db010d956 0xfc001e07c7fe3f7e 0xf873ff99f000fe67

def z741 : W := mkw 0x69552004d22c830b 0x100002004e05a383 0x000fe000073fc401 0x180000000700e387

def z742 : W := mkw 0x443002408898130a 0x0800020048840221 0x0000000000000000 0x0000000000000000

def z743 : W := mkw 0x74300248c9de5f0b 0xc800020048849377 0x00000000003ffc00 0x1c000000000003ff

def z744 : W := mkw 0x57bc9b66ac9a131a 0xe9b726004bef3665 0x03f0ffc7f8fe3d02 0xfbf300000fe71e67

def z745 : W := mkw 0x0000000000000014 0x039520a210000000 0x0c00000000000104 0x0383038070000000

def z746 : W := mkw 0x54f14ad288bb336a 0xc86217196cc616ed 0xfff01fc7f8ffff7e 0xfc731f99f8e71fff

def z747 : W := mkw 0x0000000000000094 0x03f7a5eab0000000 0xfc00000000000124 0x03f3e381f0000000

def z748 : W := mkw 0x0000000000000080 0x0301a0e090000000 0xffffe000000003af 0x0383e3e1ff000000

def z749 : W := mkw 0xf47142d8c9ff7feb 0xca4093ffec8493ff 0xfc000000003ffc0c 0x1c0003fff00003ff

def z750 : W := mkw 0x0000000000000060 0x0062151920000000 0xfc000000000003fc 0x007f1ffff0000000

def z751 : W := mkw 0x44b00a428898130a 0x0862070868c60621 0x03f001c038000000 0x0070000008e70000

def z752 : W := mkw 0x4bddb926b628831a 0x31b726004f6f2681 0x03f0e1c038000100 0x03f300000fe70000

def z753 : W := mkw 0x0000000000000060 0x00f6151920000000 0xfc000000000003fc 0x03ff1f99f0000000

def z754 : W := mkw 0x80800802000000f4 0x03fffdffb0420400 0xfc000007f8c003fc 0x63fffffff0071c00

def z755 : W := mkw 0x4ffd7ad69ab9b30a 0x1bf727aa7fef26a9 0x0ff0e1c038000104 0x03f303807fe70000

def z756 : W := mkw 0x0000000000000000 0x030120a010000000 0x0c0000000000038c 0x038303e070000000

def z757 : W := mkw 0x838e9d27240000e4 0x224091ffb37b6c00 0xffffffffffc0000f 0xe00003fffffffc00

def z758 : W := mkw 0x1000000000020060 0xc062151920001044 0xfc000000003e3f7c 0x18731f99f0000267

def z759 : W := mkw 0xe4b20e4bc9dc5f8b 0x086acf4ce8d6cf33 0x0fff01f83f01c185 0x047fe3e678ffe198

def z760 : W := mkw 0x69142004d20c8081 0x1301a0e0d205a103 0xffffe007ff0007af 0x5b83e3e1ff07e007

def z761 : W := mkw 0x80000000000000f4 0x03ddf9ffb0000000 0xfc000000000003ac 0x038fe3fff0000000

def z762 : W := mkw 0xf5968d6fedce5cf1 0xe92bfc55e257fd57 0xfc000007ffc00434 0x7803fc01f007fc07

def z763 : W := mkw 0x1080080200020060 0xc062151920421444 0xfff01fc7f8fe3f7e 0xf8731f99f8e71e67

def z764 : W := mkw 0x0000000000000084 0x0341a1eab0000000 0xfc000000000003ac 0x0383e3e1f0000000

def z765 : W := mkw 0x3de52a465ab690e1 0xdb63b5f9b6c3b5e6 0x000fffc007c1f8d1 0xa3f0fc7807e0fde0

def z766 : W := mkw 0x0000000000000080 0x0363a5e8b0000000 0xfc000000000003ac 0x03f3e3e1f0000000

def z767 : W := mkw 0xd957240d936acf6a 0xd3097ab55e157ad5 0x0ff0fe3838c03954 0xa78f1f9e7f1f1c78

def z768 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfff01fc0000003fe 0x83fffffff8e00000

def z769 : W := mkw 0x4bfdfbb6b639a31a 0x33f727aa5fef26a9 0x0ff0e1c038000104 0x03f303807fe70000

def z770 : W := mkw 0x54b00a42889a130a 0xc822060048c61665 0x03f01fc7f8fe3c32 0xf8031c0008e71e67

def z771 : W := mkw 0x7b7f769dd37fef0b 0xd00002004fbdfbff 0x03fffffffffffc03 0xfc0000000fffffff

def z772 : W := mkw 0x44b00a428898130a 0x0800020048c60621 0x03f01fc7f8c00002 0xe000000008e71c00

def z773 : W := mkw 0x405100008028030a 0x000002004c040281 0x03ffe007f83fc403 0x580000000f070387

def z774 : W := mkw 0x82495090002120f4 0x03fffdffb5280088 0xfc00e000000003fc 0x03fffffff7000000

def z775 : W := mkw 0x0945200412208080 0x1301a0e096012080 0xfc00e000000003ac 0x0383e3e1f7000000

def z776 : W := mkw 0x0080080200000000 0x0022040000420400 0xfff01fc7f8c0037e 0xe0731f81f8e71c00

def z777 : W := mkw 0x1000000000020060 0xc000101100001044 0xfc001e07c0fe3f7e 0xf8031f99f0001e67

def z778 : W := mkw 0x6b7d7294d23da38b 0x10008240cfada3ab 0xf3ffffffff3ffeeb 0xdc0ce07f8fffe3ff

def z779 : W := mkw 0xa0020401400400f5 0x03fffdffb010c902 0xfc0f1e3fc7ffc7ff 0xfbfffffff018ff87

def z780 : W := mkw 0x427952908039230a 0x02d403aa4dac02a9 0x0ffffff8383ffbcf 0x87ff03fe7fff03f8

def z781 : W := mkw 0x50300200801a036a 0xc040131948841265 0xfff01fc7f8fe3f7e 0xf8731f99f8e71e67

def z782 : W := mkw 0x69552004d22c830b 0x100002004e05a383 0x03f0e007ff000400 0x580000000f07e007

def z783 : W := mkw 0x495520049228830a 0x110122004e052281 0x03f0e00038000100 0x038300000f070000

def z784 : W := mkw 0x9002040901424ce0 0xc309f8f590105854 0xfc001e3800c03bfc 0xa78ffffff0181c78

def z785 : W := mkw 0x038e9d2724000000 0x209c4800037b6c00 0x03ffffffffc003f3 0xe3fcfc000ffffc00

def z786 : W := mkw 0x0000000000000014 0x03d521aa30000000 0x0c00000000000004 0x0380038070000000

def z787 : W := mkw 0x467952d088b9330a 0x0ad403aa6dac02a9 0x0ffffff8003ffbcf 0x87fc03fe7ff803f8

def z788 : W := mkw 0x1000000000020060 0xc062151920001044 0xfc000007c0c0077c 0x78731f99f0001c07

def z789 : W := mkw 0x57be9f67ac9a131a 0xe99d6a004bff7e65 0x03fffffffffe3c83 0xfb8ce0000ffffe67

def z790 : W := mkw 0x80000000000000f4 0x02feddffb0000000 0xfc0000000000037c 0x007f1ffff0000000

def z791 : W := mkw 0xb002040941464cf5 0xc2feddffb010d956 0xfc0f1e3fc7fffeff 0xfc7cfffff018ffff

def z792 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0xf3ffffffc03fffeb 0xdffc03ff8ff803ff

def z793 : W := mkw 0x80000000000000f4 0x036bfdffb0000000 0xfc000000000002fc 0x000ffffff0000000

def z794 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xfffffe07ff3fffef 0xdb83e3f9ff07e3e7

def z795 : W := mkw 0x80000000000000e4 0x0040915db0000000 0xfc0000000000000c 0x00000399f0000000

def z796 : W := mkw 0x6adbbd23f62c839b 0x32becee0dd7ecf83 0xfc001ff800ffc45c 0xb87c1fe1f0f81f87

def z797 : W := mkw 0xf7be9f6fedde5ffb 0xe9bffe55cbffff77 0xf3fffffffffffffb 0xfffffc7f8fffffff

def z798 : W := mkw 0x838e9d2724000094 0x23ffedeeb37b6c00 0x0fffffffffc003f7 0xe3ffffe67ffffc00

def z799 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0xfffffff8003ffbef 0x87ff03fffff803f8

def z800 : W := mkw 0x7fffbf67febe931b 0xf9bf6e004fffffe7 0x03fffffffffffff3 0xfbfffc000fffffe7

def z801 : W := mkw 0x80000000000000e4 0x024091ffb0000000 0xfc00000000000004 0x00000381f0000000

def z802 : W := mkw 0xf4320649c9de5feb 0xc808da55c894db77 0xf00f1e3fc7fffefb 0xfc0cfc7f8018ffff

def z803 : W := mkw 0x50900802800a036a 0xc022161148461645 0xfff01fc7f8fe3f7e 0xf8731f99f8e71e67

def z804 : W := mkw 0xf4b20e4bc9de5feb 0xc808da55c8d6df77 0xf3f01fc7fffe3c32 0xf800fc0188e7fe67

def z805 : W := mkw 0xb1868d2f65464cf5 0xe3fffdffb253fd56 0xfc000007ffc007fc 0x7bfffffff007fc07

def z806 : W := mkw 0x0104000400000000 0x0101200002012000 0xffffe007ff0003af 0x4383e381ff07e000

def z807 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc000000000003f4 0x03ffff81f0000000

def z808 : W := mkw 0x80000000000000e4 0x02dcd9ffb0000000 0xfc000000000003fc 0x03fcfffff0000000

def z809 : W := mkw 0xb000000841464cf5 0xc3fffdffb0009156 0xfc0f1e38003fffff 0x9ffffffff01803ff

def z810 : W := mkw 0x80000000000000e4 0x024091ffb0000000 0xfc0f1e38003ffacf 0x840c03fff01803f8

def z811 : W := mkw 0x030e952524000090 0x239de8e093396800 0xfc0fe038070003ad 0x038fe3e1f718e000

def z812 : W := mkw 0x89452004122080f4 0x13fffdffb6012080 0xfc00e000000003fc 0x03fffffff7000000

def z813 : W := mkw 0x495520049228830a 0x130122a05e052281 0x03f0e00038000000 0x038000000f070000

def z814 : W := mkw 0x038e9d2724000010 0x21ff6d08237b6c00 0x0fffffffffc003f7 0xe3ffff807ffffc00

def z815 : W := mkw 0x77be9f6fedde5f1b 0xe9bf6e004bffff77 0x03fffffffffffff3 0xfffffc000fffffff

def z816 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xfff01fc7f8c00776 0xf8731f81f8e71c07

def z817 : W := mkw 0x7d752244dabe930b 0xd80002004e85b3e7 0x03ffe007ff3ffc03 0x580000000f07e3e7

def z818 : W := mkw 0x9002040901424ce4 0xc248d9ffb0105854 0xfc001e3800c0385c 0xa40c1ffff0181c78

def z819 : W := mkw 0x55b68f67ac9a130a 0xe80002004ad77e65 0x03f01fc7fffe3c02 0xf800000008e7fe67

def z820 : W := mkw 0x038c180600000000 0x01b72400036b2400 0x03ffffffffc003f3 0xe3fffc000ffffc00

def z821 : W := mkw 0x6b3c7294d21da081 0x11d5a14ad3ada12b 0xfc001fffff003c64 0xdc7fe01ff0ffe07f

def z822 : W := mkw 0x6bdfbd27f62c839b 0x339deae0df7fef83 0x03ffffffffffc483 0xfb8ce0600fffff87

def z823 : W := mkw 0x0000000000000004 0x02d401aa30000000 0x0c00000000000104 0x03f0038070000000

def z824 : W := mkw 0x7dd52846daae930b 0xd80002004e47b7c7 0x03ffe007ffffc403 0x780000000f07ff87

def z825 : W := mkw 0x0000000000000060 0x0022141120000000 0xfc0000000000033c 0x00031f81f0000000

def z826 : W := mkw 0x028a9d2324000090 0x23bfece0917a4c00 0xfc001ff800c003fc 0xa3ffffe1f0f81c00

def z827 : W := mkw 0x0228529000112000 0x00d4010a01a80028 0x03fffff8003ffbcb 0x87fc007e0ff803f8

def z828 : W := mkw 0xb106040d41464ce1 0xc309f8f59211f956 0xfffffe3fffffffff 0xff8fffffff1fffff

def z829 : W := mkw 0xfc712240dabe93ef 0xda4093fffc8493e7 0xfc000000003ffc0c 0x180003fff00003e7

def z830 : W := mkw 0xe9552004d22c83eb 0x1008da55ce05a383 0xf3ffe007ff3fc6fb 0x580cfc7f8f07e387

def z831 : W := mkw 0xb002040941464cf5 0xc3ddf9ffb010d956 0xfc0f1e3fc7fffeff 0xff8cfffff018ffff

def z832 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc0000000000018c 0x03ffe3fff0000000

def z833 : W := mkw 0x96aa5edb09d37c60 0xc8fe5d1f21fa5c7c 0x00001ff800c03850 0xa47c1c1e00f81c78

def z834 : W := mkw 0x68512000d22c838b 0x120082e0dc048383 0x00000000003fc400 0x1800006000000387

def z835 : W := mkw 0x80000000000000e4 0x024091ffb0000000 0xfc000000000002ac 0x0000e3fff0000000

def z836 : W := mkw 0x82081000000000f4 0x03fffdffb1280000 0xfc0fe038000003fd 0x03fffffff7180000

def z837 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x03ffe1ffffc001b1 0x63fffc000ffffc00

def z838 : W := mkw 0x0000000000000080 0x0301a0e090000000 0xfc000000000003ec 0x038fe3fff0000000

def z839 : W := mkw 0x82495090002120f4 0x03fffdffb5280088 0xfc0ffe38003ffbff 0x87fffffff71803f8

def z840 : W := mkw 0xb4a20e4b49d65ce1 0xc86add5da0d2dd76 0xfc0f1fffc7ffffff 0xfc7ffffff0f8ffff

def z841 : W := mkw 0xa24b549941656cf5 0x03fffdffb538c99a 0xfc0fe0380701c3fd 0x07fffffff718e198

def z842 : W := mkw 0x81040004000000f4 0x03fffdffb2012000 0xfc0fe000070003fd 0x03fffffff700e000

def z843 : W := mkw 0x0000000000000000 0x0101200000000000 0xfc000000000003ac 0x0383e381f0000000

def z844 : W := mkw 0x830c9124240000f4 0x23fffdffb3292000 0xfc00e000000003fc 0x03fffffff7000000

def z845 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0x03f01fc7f8fe3f72 0xf8731c1808e71e67

def z846 : W := mkw 0x80820c03000000e0 0x006add5da0524c00 0xffff1fffffc003ff 0xe07ffffff8fffc00

def z847 : W := mkw 0xf957240dd36ecfeb 0xd109fa55ce15fbd7 0xf3fffe3ffffffffb 0xff8ffc7f8f1fffff

def z848 : W := mkw 0xfdf72e4fdbfedfeb 0xd808da55ced7fff7 0xf3fffffffffffefb 0xfc0cfc7f8fffffff

def z849 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0x000f1e3fc7fffcd3 0xfc0cfc7e0018ffff

def z850 : W := mkw 0x495520049228830a 0x110122004e052281 0x03ffe007ff0003a3 0x4383e0000f07e000

def z851 : W := mkw 0x0208100000000060 0x00f6151921280000 0xfffffff8000003ff 0x83ff1f99fff80000

def z852 : W := mkw 0x01868d2724000070 0x216b7d1922536c00 0xfc000007ffc0037c 0x6073ff99f007fc00

def z853 : W := mkw 0x838e9d27240000f4 0x21fffd5db37b6c00 0xffffffffffc003ff 0xe3ffff99fffffc00

def z854 : W := mkw 0xb002040941464cf5 0xc3fffdffb010d956 0xfc001e3800fffffc 0xbffffffff0181fff

def z855 : W := mkw 0x928a9d2b25424cf4 0xe3fffdffb17a5c54 0xfc001ff800c03bfc 0xa7fffffff0f81c78

def z856 : W := mkw 0xb947240d5366cce1 0xd309f8f59611f9d6 0xfc0ffe3fc7ffffff 0xff8ffffff718ffff

def z857 : W := mkw 0x82695290003123fe 0x012bfe55bda802a8 0xfffffff8003ff837 0x8403fc01fff803f8

def z858 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0x00001fc000fe3c50 0xb8701c1800e01e67

def z859 : W := mkw 0x6b5d3004d22c830b 0x100002004f2da383 0x03ffffffff3fc403 0xd80000000fffe387

def z860 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xfff001c7f8fe073e 0x78731f81f8e71e07

def z861 : W := mkw 0x69552004d22c830b 0x100002004e05a383 0x03ffe007ff3fc68b 0x580000600f07e387

def z862 : W := mkw 0x47bc9b66ac98130a 0x280002004bef2621 0x03f0e1c038000000 0x000000000fe70000

def z863 : W := mkw 0xb30e952d65464cf5 0xe3fffdffb339f956 0xfc0ffe3fc7ffffff 0xfffffffff718ffff

def z864 : W := mkw 0x8000000000000094 0x03ffedeeb0000000 0x0c000000000003f4 0x03ffffe670000000

def z865 : W := mkw 0xd4b00a42889a136e 0xc862171f68c61665 0xfff01fc7f8fe3f7e 0xf8731f9ff8e71e67

def z866 : W := mkw 0x54b00a42889a131a 0xc9bf6e0048c61665 0x03f01fc7f8fe3ff2 0xfbfffc0008e71e67

def z867 : W := mkw 0x0000000000000080 0x0301a0e090000000 0x0c00000000000184 0x0383e3e070000000

def z868 : W := mkw 0x46f95ad288b9330a 0x080002004dee06a9 0x03f0e1c038000000 0x000000000fe70000

def z869 : W := mkw 0x2104000440040081 0x0301a0e09201a102 0xffffe007ff3fc7af 0x5b83e3e1ff07e387

def z870 : W := mkw 0x80000000000000e0 0x03ddf9ff90000000 0xfc000000000003fc 0x03fffffff0000000

def z871 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xfffffe3fff3fffaf 0xdf83e3e1ff1fe3ff

def z872 : W := mkw 0x78532409d36ecf0b 0xd00002004c14dbd7 0x000f1e3fc7fffc03 0xfc0000000018ffff

def z873 : W := mkw 0x0945200412208014 0x13f725aa36012080 0x0c00e00000000104 0x03f3038077000000

def z874 : W := mkw 0x838e9d27240000f4 0x23fffdffb37b6c00 0xfff0e1c7ffc00134 0x63f3ff81ffe7fc00

def z875 : W := mkw 0x82285290001120f4 0x03fffdffb1a80028 0xfc0001c0000003fc 0x03fffffff0e00000

def z876 : W := mkw 0x2841200052248081 0x120080e094008182 0xfc0000000001c00c 0x000003e1f0000180

def z877 : W := mkw 0xb1868d2f65464cf5 0xe12bfc55b253fd56 0xfc000007ffc00434 0x7803fc01f007fc07

def z878 : W := mkw 0xb002040941464ce5 0xc008d855b010d956 0xfc0f1e3fc7fffeff 0xfc0cfc7ff018ffff

def z879 : W := mkw 0x57ffdff7acbb330a 0xe80002004fff7eed 0x03fffffffffffc03 0xfc0000000fffffff

def z880 : W := mkw 0x030e140500000000 0x019d680003396800 0x03ffffffffc003f3 0xe3fffc000ffffc00

def z881 : W := mkw 0xb002040941464ce5 0xc24091ffb010d956 0xfc0f1e3fc7fffc0f 0xfc0003fff018ffff

def z882 : W := mkw 0x8000000000000084 0x020080e690000000 0xfc0000000000000c 0x000003e7f0000000

def z883 : W := mkw 0x79552004d22e830b 0xd00002004e05b3c7 0x03fffe07fffffc03 0xf80000000f07ffe7

def z884 : W := mkw 0xa947240d5364ccf5 0x13fffdffb611e992 0xfc0fe0380701c3fd 0x07fffffff718e198

def z885 : W := mkw 0x80000000000000f4 0x0349f9ffb0000000 0xfc0000000000000c 0x0000e3fff0000000

def z886 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x03ffe1c7ffc003b3 0x63f3fc000fe7fc00

def z887 : W := mkw 0x2002040140040091 0x03bfece09010c902 0xfc0f1e3fc7ffc7ff 0xfbffffe1f018ff87

def z888 : W := mkw 0x80000000000000f4 0x016bfd5db0000000 0xfc00000000000134 0x0073ff81f0000000

def z889 : W := mkw 0x60510000c02c038b 0x020082e0cc048383 0xffffe007ff3fc7af 0x5b83e3e1ff07e387

def z890 : W := mkw 0x0228529000112014 0x03f725aa31a80028 0x0c0001c000000104 0x03f3038070e00000

def z891 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0xf3ff1e3ffffffffb 0xfc0ffc7f881fffff

def z892 : W := mkw 0x573e9765ac9a137a 0xe9dd7b196bbd7a65 0xfc0fe038073e3c8d 0x1b8ce399f718e267

def z893 : W := mkw 0xb38c992e65464cf1 0xe1b7b455836bb556 0xf3f0e1c0383ffd08 0x1ff3007f8fe703ff

def z894 : W := mkw 0x54f10a4288ba130a 0xc80002004cc616e5 0x03ffffc7f8fffc03 0xf80000000fe71fe7

def z895 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0x03ffe1f8003ff989 0x07fc03fe0ff803f8

def z896 : W := mkw 0x6bdfbd27f62c831b 0x30be4e004f7fef83 0x03ffffffffffc453 0xf87c1c000fffff87

def z897 : W := mkw 0x024910000020030a 0x029402a00d280280 0x03fffff8003ffbcb 0x87fc03fe0ff803f8

def z898 : W := mkw 0x44b00a428898130a 0x0800020048c60621 0x03f001c7f83e0402 0x5800000008e70207

def z899 : W := mkw 0x60100000c00c030b 0x0000020048048303 0x03ff0007ff3fc403 0x580000000807e387

def z900 : W := mkw 0x81868d27240000f4 0x232bfcf5b2536c00 0xffffe007ffc003bf 0x6383ffe1ff07fc00

def z901 : W := mkw 0x0000000000000074 0x03ff7dbb30000000 0xfc000000000003fc 0x03ffff99f0000000

def z902 : W := mkw 0xa8412000522480e5 0x124091ffb4008182 0xfc0000000001c00c 0x000003fff0000180

def z903 : W := mkw 0x838c9926240000f4 0x23fffdffb36b2400 0xfff0ffc7f8c003fe 0xe3ffffffffe71c00

def z904 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc000000000000dc 0x03fcfffff0000000

def z905 : W := mkw 0xa002040941444c95 0x039de8e69010c912 0xfc0f003fc73fc7af 0x5f8fe3e7f018e39f

def z906 : W := mkw 0xab4fb525762480f5 0x33fffdffb739e982 0xfc0fe0380701c3fd 0x03fffffff718e180

def z907 : W := mkw 0xab4fb52576248095 0x339de8e69739e982 0x000fe0380701c081 0x038ce0660718e180

def z908 : W := mkw 0x0000000000000010 0x03bf6ca010000000 0x0c000000000003f4 0x03ffff8070000000

def z909 : W := mkw 0x828a9d23240000f4 0x23fffdffb17a4c00 0xfc0f1fffc7c003ff 0xe3fffffff0f8fc00

def z910 : W := mkw 0x038e9d2724000094 0x23ffedeab37b6c00 0xffffffffffc003ff 0xe3ffffe1fffffc00

def z911 : W := mkw 0x7c7162d0dabfb3eb 0xda4093fbfc8493ef 0xfc000000003ffc0c 0x1c0003fff00003ff

def z912 : W := mkw 0x030c100400000080 0x03d5a1ea93292000 0xffffffffff0003ef 0xc3ffe3ffffffe000

def z913 : W := mkw 0x56ba9f63ac9a130a 0xe800020049fe5e65 0x03f01ffff8fe3c02 0xf800000008ff1e67

def z914 : W := mkw 0x828a9d2324000074 0x20fe5d1f217a4c00 0xfff01ffff8c0037e 0xe07f1f9ff8ff1c00

def z915 : W := mkw 0x2000000040040081 0x0301a0e090008102 0xfc0f00000701c3ad 0x0383e3e1f000e180

def z916 : W := mkw 0x0104000400000000 0x030120a012012000 0x0fffe007ff0003a7 0x4383e3807f07e000

def z917 : W := mkw 0x80000000000000f4 0x01fffd5db0000000 0xfc000000000003fc 0x03ffff99f0000000

def z918 : W := mkw 0x96a85ad2089330f4 0xcbfffdffb1ea146c 0xfc001ff800c03bfc 0xa7fffffff0f81c78

def z919 : W := mkw 0x80410000002000f4 0x03fffdffb4000080 0xfc0fe0000001c3fd 0x03fffffff7000180

def z920 : W := mkw 0x038eddb724012010 0x21bf6c02037b6c08 0x03ffffffffc003f3 0xe7fffc060ffffc18

def z921 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xffff1ffff8ffff7f 0xfc731f99f8ff1fff

def z922 : W := mkw 0xa30e952d65444c95 0x239de8e69339e912 0x000fe0380701c081 0x078ce0660718e198

def z923 : W := mkw 0xa30e952d65444cf5 0x23fffdffb339e912 0xfc0fe0380701c3fd 0x07fffffff718e198

def z924 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0xffffffffffc003ff 0xe3ffff81fffffc00

def z925 : W := mkw 0x8000000000000080 0x0309e8e490000000 0xfc000000000003ac 0x038fe3e7f0000000

def z926 : W := mkw 0x7df52a46dabe930b 0xd92326004ec7b7e7 0x03ffffc7fffffff3 0xfbf3fc000fe7ffe7

def z927 : W := mkw 0xa9452004522480f5 0x13fffdffb601a182 0xfc0fe007c73fc7ff 0x5bfffffff700e387

def z928 : W := mkw 0x80000000000000f4 0x02f695ffb0000000 0xfc0000000000000c 0x007003fff0000000

def z929 : W := mkw 0x55b40a46889a130a 0xc80002004ac73665 0x03ffffc7fffe3c03 0xf80000000fe7fe67

def z930 : W := mkw 0xb000000841464ce1 0xc040915da0009156 0xfc000000003ffc0c 0x1c0003fff00003ff

def z931 : W := mkw 0x80000000000000f4 0x032bfcf5b0000000 0xfc00000000000134 0x0383ff81f0000000

def z932 : W := mkw 0x038e9d2724000090 0x23ffedea937b6c00 0xffffffffffc003ff 0xe3fffffffffffc00

def z933 : W := mkw 0x0269529000312000 0x02d401aa05a800a8 0x03fffff80001fbc3 0x87fc007e0ff801f8

def z934 : W := mkw 0x0104000400000000 0x030120a012012000 0x0ff0e00038000104 0x038303807f070000

def z935 : W := mkw 0x6b5d3004d22c830b 0x109402004f2da383 0x03ffffffff3fc7c3 0xdbfc00000fffe387

def z936 : W := mkw 0x55b68f67ac9a131a 0xe92b6e004ad77e65 0x03f01fc7fffe3c32 0xf803fc0008e7fe67

def z937 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0x000fe000073fc481 0x1b80e0600700e387

def z938 : W := mkw 0x834fd5b5242120f4 0x23fffdffb7396888 0xfc0fe0380701c3fd 0x07fffffff718e198

def z939 : W := mkw 0x80000000000000e4 0x024091ffb0000000 0xfc000000003ff80c 0x040003fff00003f8

def z940 : W := mkw 0x411400048008030a 0x000002004a052201 0x03ffe007ff3e0403 0x580000000f07e207

def z941 : W := mkw 0x0000000000000094 0x03ffedeab0000000 0xfc000000000003fc 0x03ffffe1f0000000

def z942 : W := mkw 0x838e9d2724000094 0x23bfece6937b6c00 0xffffffffffc003ff 0xe3ffffe7fffffc00

def z943 : W := mkw 0x0080080200000060 0x0062151920420400 0xfc000007f8c0037c 0x60731f99f0071c00

def z944 : W := mkw 0x74b20e4bc9de5f0b 0xc800020048d6df77 0x03f01fc7fffe3c02 0xf800000008e7fe67

def z945 : W := mkw 0x1000000000020060 0xc040111920001044 0xfc000000003e3c0c 0x18000399f0000267

def z946 : W := mkw 0x0080080200000000 0x0062050820420400 0x0ff001c038000104 0x0073038078e70000

def z947 : W := mkw 0x0000000000000000 0x02d401aa00000000 0xfc000000000003ec 0x03ff03fff0000000

def z948 : W := mkw 0x038e9d2724000000 0x21232400037b6c00 0x03ffffffffc003f3 0xe3f3fc000ffffc00

def z949 : W := mkw 0x54b20e4b89da5f0a 0xc800020048d65e75 0x03f01ffff8fe3c02 0xfc00000008ff1e7f

def z950 : W := mkw 0x80000000000000f4 0x036bfdffb0000000 0xfc000000000003bc 0x0383fffff0000000

def z951 : W := mkw 0x80828d23240000f4 0x23fffdffb0524c00 0xfc00000000c003fc 0x23fffffff0001c00

def z952 : W := mkw 0xa9042004520480f5 0x13fffdffb201a102 0xfc000000070003fc 0x03fffffff000e000

def z953 : W := mkw 0x8000000000000094 0x03ffedeeb0000000 0x0c000000000003cc 0x03ffe3fe70000000

def z954 : W := mkw 0xb002040941464ce1 0xc3ddf9ff9010d956 0xfc0f1e3fc7ffffff 0xfffffffff018ffff

def z955 : W := mkw 0x038c992624000094 0x23f7a5eab36b2400 0xffffe1c7ff0003af 0x43f3e3e1ffe7e000

def z956 : W := mkw 0x0269529000312000 0x02d401aa05a800a8 0x000ffff80001fbc9 0x87fc03fe07f801f8

def z957 : W := mkw 0xb002040941464cf5 0xc0fedd5fa010d956 0xfc0f1e3fc7ffffff 0xfc7ffffff018ffff

def z958 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xffffe007ff0007a7 0x5b83e381ff07e007

def z959 : W := mkw 0xab4f749d5365ec81 0x139de8e69739e99a 0x000fe0380701c081 0x078ce0660718e198

def z960 : W := mkw 0x96aa9f632c9210f4 0xebfffdffb1fa5c64 0xfc001ff800c03bfc 0xa3fffffff0f81c60

def z961 : W := mkw 0x44b00a428898130a 0x0862070868c60621 0xfff01fc7f8fe077e 0xf8731f81f8e71e07

def z962 : W := mkw 0xa0000000400400e5 0x024091ffb0008102 0xfc0f0007c73fc6af 0x5800e3fff000e387

def z963 : W := mkw 0xb38e9d2f65464cf1 0xe1fffd5da37bfd56 0xffffffffffffffff 0xffffffffffffffff

def z964 : W := mkw 0x80000000000000e4 0x0248d9ffb0000000 0xfc0000000000008c 0x000ce3fff0000000

def z965 : W := mkw 0x0000000000000000 0x030120a010000000 0xfc0000000000032c 0x03830381f0000000

def z966 : W := mkw 0x7957240dd36ecf0b 0xd00002004e15fbd7 0x03ffe007ffffc403 0x780000000f07ff87

def z967 : W := mkw 0x567952d088bb330a 0xc80002004dac12ed 0x03fffff8003ffc03 0x9c0000000ff803ff

def z968 : W := mkw 0xb106040d41464cf5 0xc3fffdffb211f956 0xfffffe3fffffffff 0xffffffffff1fffff

def z969 : W := mkw 0xabcfbd27762480f5 0x33fffdffb77bed82 0xffffffffffc1c3ff 0xe3fffffffffffd80

def z970 : W := mkw 0x038c992624000010 0x21b72400036b2400 0x03ffffc7ffc003f3 0xe3f3fc000fe7fc00

def z971 : W := mkw 0x8000000000000074 0x03ff7dbf30000000 0xfc0000000000037c 0x03ff1f9ff0000000

def z972 : W := mkw 0xf957240dd36ecf8b 0xd309eae4de15fbd7 0x03fffe3ffffffc83 0xff8ce0660f1fffff

def z973 : W := mkw 0x56f95ad288bb330a 0xc8b606004dee16ed 0x03fffffff8fffff3 0xffff1c000fff1fff

def z974 : W := mkw 0x0000000000000014 0x03f725aa30000000 0x0c0f1e38003ffbcf 0x87ff03fe701803f8

def z975 : W := mkw 0xb002040941464ce1 0xc048d95da010d956 0xfc0f1e3fc7fffeff 0xfc0cfffff018ffff

def z976 : W := mkw 0xb28a9d2b65464cf5 0xe3fffdffb17add56 0xfc0f1fffc7ffffff 0xfffffffff0f8ffff

def z977 : W := mkw 0x00000000000000e0 0x024091f9b0000000 0xfc0000000000000c 0x000003f9f0000000

def z978 : W := mkw 0x6bffffb7f63da30b 0x300002004fffefab 0x03fffffffffffc03 0xfc0000000fffffff

def z979 : W := mkw 0x80000000000000f4 0x02feddffb0000000 0xfc000000000003dc 0x03fc1ffff0000000

def z980 : W := mkw 0x80020401000000f4 0x03fffdffb0104800 0xfc000007c7c003fc 0x63fffffff000fc00

def z981 : W := mkw 0x96aa9f6b2dd25c70 0xe8fe5d1d21fa5c74 0x00001ff800c03850 0xa47c1c1e00f81c78

def z982 : W := mkw 0x028a9d2324000014 0x23ff6daa317a4c00 0x0c001ff800c00154 0xa3ff1f8070f81c00

def z983 : W := mkw 0x0208100000000000 0x02d401aa01280000 0x03fffff8003ffbcb 0x87fc03fe0ff803f8

def z984 : W := mkw 0x00000000000000e0 0x0301b0f190000000 0xfc000000000003fc 0x0383fff9f0000000

def z985 : W := mkw 0x6957240dd36ccf0b 0x100002004e15eb93 0x03ffe03fff3fc403 0x5c0000000f1fe39f

def z986 : W := mkw 0x54900842888a136a 0xc822161168461645 0xfff01fc7f8fe077e 0xf8731f81f8e71e07

def z987 : W := mkw 0xb22a569941576cf5 0xc3fffdffb1b8d97e 0xfc0f1fffc7ffffff 0xfffffffff0f8ffff

def z988 : W := mkw 0x0000000000000060 0x0062151920000000 0xfc00000000000134 0x00731f81f0000000

def z989 : W := mkw 0x94200240089210e4 0xca4091ffb0801064 0xfc0000000000380c 0x000003fff0000060

def z990 : W := mkw 0x838e9d2724000074 0x21ff7d1f237b6c00 0xffffffffffc003ff 0xe3ffff9ffffffc00

def z991 : W := mkw 0xe9552004d22c839f 0x139deae6de05a383 0x03ffe007ff3fc483 0x5b8ce0660f07e387

def z992 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc000000000000bc 0x038ffffff0000000

def z993 : W := mkw 0x82285290001120e4 0x02d491ffb1a80028 0xfc001ff80000384c 0x847c03fff0f80078

def z994 : W := mkw 0x0000000000000094 0x0323a4e0b0000000 0xfc000000000003ac 0x0383e3e1f0000000

def z995 : W := mkw 0x54300240889a136a 0xc800121148841265 0xf0001e07c0fe3e7a 0xf8001c1980001e67

def z996 : W := mkw 0x0000000000000064 0x024011bb30000000 0xfc0000000000000c 0x00000399f0000000

def z997 : W := mkw 0x427952908039230a 0x02d403aa4dac02a9 0x03fffffff83fffcb 0xdffc03fe0fff03ff

def z998 : W := mkw 0x838e9d27240000f4 0x23fffdffb37b6c00 0xffffe1f83f0003fd 0x03ffffffffffe000

def z999 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x03ffffffffc000d3 0xe3fcfc000ffffc00

def z1000 : W := mkw 0x81868d27240000f4 0x236bfdffb2536c00 0xfc000007ffc0003c 0x6003fffff007fc00

def z1001 : W := mkw 0x74320649c9de5f0b 0xc80002004894db77 0x000f1e3fc7fffc03 0xfc0000000018ffff

def z1002 : W := mkw 0x1420024008921060 0xc862151920801064 0xfc00000000003b7c 0x00731f99f0000060

def z1003 : W := mkw 0xb947240d5366ccf5 0xd3fffdffb611f9d6 0xfc0ffe3fc7ffffff 0xfffffffff718ffff

def z1004 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xf3f01fc7f8fe3e7a 0xf8701c1988e71e67

def z1005 : W := mkw 0x0000000000000000 0x020000a010000000 0x0c00000000000004 0x0000038070000000

def z1006 : W := mkw 0x69552004d22c838b 0x10008240ce05a383 0x03ffe007ff3fc483 0x5800e0600f07e387

def z1007 : W := mkw 0x8000000000000074 0x03ff7dbf30000000 0x0c00000000000114 0x03f31f8070000000

def z1008 : W := mkw 0x0020020000100060 0x0062151920800020 0xfc001fc000003b7c 0x80731f99f0e00060

def z1009 : W := mkw 0x80000000000000f4 0x032bfcf5b0000000 0xfc000000000003fc 0x038ffffff0000000

def z1010 : W := mkw 0x61140004c00c038b 0x0101a240ca05a303 0xffffe007ff3fc7af 0x5b83e3e1ff07e387

def z1011 : W := mkw 0x0000000000000014 0x03f725aa30000000 0x0c00000000000184 0x03ff03e670000000

def z1012 : W := mkw 0x81040004000000e4 0x0341b1ffb2012000 0xffffe007ff0003af 0x4383e3ffff07e000

def z1013 : W := mkw 0x8000000000000064 0x0062151f20000000 0xfc0000000000037c 0x00731f9ff0000000

def z1014 : W := mkw 0xb002040941464cf1 0xc3bffcf59010d956 0xfc0f1e3fc7ffffff 0xfffffffff018ffff

def z1015 : W := mkw 0x0228529000112060 0x00f6151b21a80028 0xfc001ff800003b7c 0x847f1f9ff0f80078

def z1016 : W := mkw 0xb002040941464ce1 0xc06add5da010d956 0xfc000007c7c0077c 0x7873ff99f000fc07

def z1017 : W := mkw 0x80000000000000f0 0x01fffd5da0000000 0xfc000000000003fc 0x03fffffff0000000

def z1018 : W := mkw 0x74b20e4bc9de5f0b 0xc82a4e0048d6df77 0x03ff1ffffffffff3 0xfc7ffc0008ffffff

def z1019 : W := mkw 0x69552004d22c830b 0x100002004e05a383 0x03ffe007ff3fc6a3 0x5800e0000f07e387

def z1020 : W := mkw 0x14a00a4208921074 0xcbf735bb30c21464 0x0c001fc000c03954 0xa3f31f9870e01c60

def z1021 : W := mkw 0x238e9d2764040091 0x23bfece0937bed02 0xffffffffffffc7ff 0xfbffffe1ffffff87

def z1022 : W := mkw 0x01868d2724000090 0x232bece092536c00 0xfc000007ffc003bc 0x6383ffe1f007fc00

def z1023 : W := mkw 0x4b7d72949239a30a 0x100002004fad22a9 0x03f0e1c038000000 0x000000000fe70000

def z1024 : W := mkw 0x838e9d27240000f4 0x23fffdffb37b6c00 0xfffffffffffffbff 0xe7fffffffffffff8

def z1025 : W := mkw 0x80000000000000e4 0x0248d9ffb0000000 0xfc0000000000003c 0x0000fffff0000000

def z1026 : W := mkw 0x14a00a4208921060 0xc862151920c21464 0xfff01fc7f8c03b7e 0xe0731f99f8e71c60

def z1027 : W := mkw 0x485120009228830a 0x100002004c040281 0x0000000000000000 0x0000000000000000

def z1028 : W := mkw 0x80000000000000f4 0x036bfdffb0000000 0xfc00000000000034 0x0003ff81f0000000

def z1029 : W := mkw 0x17ae9f672c921070 0xe9ff7d1923fb7c64 0xffffffffffc03bff 0xe3ffff99fffffc60

def z1030 : W := mkw 0x0000000000000074 0x03f735bb30000000 0xfc0000000000010c 0x03f30399f0000000

def z1031 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0xf0001e3fc7fffc78 0xfc0cfc7f8018ffff

def z1032 : W := mkw 0x80000000000000e0 0x0309f8f590000000 0xfc000000000003bc 0x0383ffe1f0000000

def z1033 : W := mkw 0x8000000000000094 0x03bfece690000000 0xfc000000000003fc 0x03ffffe7f0000000

def z1034 : W := mkw 0x14a00a4208921060 0xc862151920c21464 0xfc001fc000c0385c 0xa0701f99f0e01c60

def z1035 : W := mkw 0x838e9d2724000014 0x21bf6c06037b6c00 0x03ffffffffc003f3 0xe3fffc060ffffc00

def z1036 : W := mkw 0x4bdfbd27b628830a 0x300002004f7f6e81 0x03ffffffffc00003 0xe00000000ffffc00

def z1037 : W := mkw 0x0249509000212080 0x0395a0e295280088 0xfc0fe0380001c3ad 0x078fe3e7f7180198

def z1038 : W := mkw 0x0000000000000014 0x03f725aa30000000 0x0c00000000000374 0x03f31f8070000000

def z1039 : W := mkw 0x0000000000000010 0x03b724a010000000 0x0c00000000000104 0x03f3038070000000

def z1040 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0xfc0f1e3fc7ffffff 0xfc0ffffff018ffff

def z1041 : W := mkw 0x84a00a42089010f4 0x0bfffdffb0c20420 0xfc0001c0000003fc 0x03fffffff0e00000

def z1042 : W := mkw 0x57ffdff7acbb331a 0xe9bf6e004fff7eed 0x03fffffffffffff3 0xfffffc000fffffff

def z1043 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xfff01fc7f8c03d74 0xf8731f99f8e71c67

def z1044 : W := mkw 0x0000000000000090 0x039de8e090000000 0xfc000000000003ac 0x038fe3e1f0000000

def z1045 : W := mkw 0x69552004d22c838b 0x10008240ce05a383 0xf3ffe007ff3fc40b 0x580000618f07e387

def z1046 : W := mkw 0x838c9926240000f4 0x23fffdffb36b2400 0xffffe1c7ff0003ff 0x43ffffffffe7e000

def z1047 : W := mkw 0x0000000000000000 0x0040010800000000 0xfc0000000000036c 0x00730399f0000000

def z1048 : W := mkw 0x81868d27240000f4 0x23fffdffb2536c00 0xffffe007ffc003ff 0x63ffffffff07fc00

def z1049 : W := mkw 0xa8412000522480f5 0x13fffdffb4008182 0xfc0000000001c3fc 0x03fffffff0000180

def z1050 : W := mkw 0x68512000d22c830b 0x100002004c048383 0x000f0007c73fc403 0x580000000000e387

def z1051 : W := mkw 0x401000008008030a 0x0000020048040201 0x03f0000038000000 0x0000000008070000

def z1052 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xfff01fc038fe3d5c 0xb8731f99f8e71e67

def z1053 : W := mkw 0x028a9d2324000070 0x20fe5d19217a4c00 0xfc001ff800c0037c 0xa07f1f99f0f81c00

def z1054 : W := mkw 0x97ae9f672c9210f4 0xebfffdffb3fb7c64 0xffffffffffc03bff 0xe3fffffffffffc60

def z1055 : W := mkw 0x0000000000000060 0x0062151920000000 0x0c00000000000154 0x00731f9870000000

def z1056 : W := mkw 0x47be9f67ac98130a 0x280002004bff6e21 0x03ffffffffc00003 0xe00000000ffffc00

def z1057 : W := mkw 0x9002040901424c74 0xc3ff7dbf30105854 0x0c001e3800c03954 0xa7ff1f9e70181c78

def z1058 : W := mkw 0x01e7cfb72431231a 0x236b6faa0ed36ea8 0x00000007fffff838 0x6403fffe0007fff8

def z1059 : W := mkw 0x69552004d22c830b 0x110122004e05a383 0x03ffe007ff3fc423 0x5803e0000f07e387

def z1060 : W := mkw 0x54b00a42889a130a 0xc800020048c61665 0x03ff1ffff8fffc03 0xfc00000008ff1fff

def z1061 : W := mkw 0x69552004d22c830b 0x100002004e05a383 0x03fffe3fff3ffc03 0xdc0000000f1fe3ff

def z1062 : W := mkw 0x82285290001120f4 0x03fffdffb1a80028 0xfffffff800003bff 0x87fffffffff80078

def z1063 : W := mkw 0x69552004d22c830b 0x100002004e05a383 0xf3ffe007ff3fc62b 0x580000018f07e387

def z1064 : W := mkw 0x80000000000000e4 0x026addffb0000000 0xfc000000000003fc 0x007ffffff0000000

def z1065 : W := mkw 0x6b5fb525f62c831b 0x319d6a004f3deb83 0x03ffe03fff3fc483 0x5b8ce0000f1fe387

def z1066 : W := mkw 0x026952900031230a 0x009402000da802a8 0x03fffff8003ffbcb 0x87fc007e0ff803f8

def z1067 : W := mkw 0x54b04ad2889b336a 0xc862171b68c6166d 0xfff01fc7f8fe3f7e 0xfc731f9ff8e71e7f

def z1068 : W := mkw 0xb38e9d2f65464cf5 0xe3fffdffb37bfd56 0xffffffffffc007ff 0xfbfffffffffffc07

def z1069 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0x03ffffffc73ffbeb 0xc7fce3fe0ff8e3f8

def z1070 : W := mkw 0x54b00a42889a130a 0xc800020048c61665 0x03f01fc7f8fe3e72 0xf8001c0008e71e67

def z1071 : W := mkw 0x0002040100000080 0x0309e8e090104800 0xfc0f1e3fc7c003ff 0xe38fffe1f018fc00

def z1072 : W := mkw 0x026952900031230e 0x02d403aa3da802a8 0x0ffffff8003ffbcf 0x87fc03fe7ff803f8

def z1073 : W := mkw 0x80000000000000f4 0x036bfdfdb0000000 0xfc000000000003fc 0x03f3fff9f0000000

def z1074 : W := mkw 0xe9552004d22c838f 0x1301a2e6de05a383 0xffffe007ff3fc7af 0x5b83e3e7ff07e387

def z1075 : W := mkw 0x8000000000000094 0x03dde9eeb0000000 0x0c00000000000084 0x038ce3e670000000

def z1076 : W := mkw 0xb002040941464cf5 0xc3fffdffb010d956 0xfc0f1e3807c1fbfd 0xa7fffffff018fdf8

def z1077 : W := mkw 0x8000000000000074 0x03ff7dbf30000000 0x0c000000000003dc 0x03ff1ffe70000000

def z1078 : W := mkw 0x828a9d23240000f4 0x22feddffb17a4c00 0xfc001ff800c0005c 0xa07c1ffff0f81c00

def z1079 : W := mkw 0x0000000000000094 0x03f7a5eab0000000 0xfc0000000000010c 0x03f303e1f0000000

def z1080 : W := mkw 0x0080080200000060 0x0062151920420400 0xfff001c03800037c 0x00731f99f8e70000

def z1081 : W := mkw 0x0000000000000070 0x03ff7dbb20000000 0xfc000000000003fc 0x03fffffff0000000

def z1082 : W := mkw 0x547142d088bb330a 0xc80002004c8412ed 0x00000000003ffc00 0x1c000000000003ff

def z1083 : W := mkw 0x54b00a42889a130a 0xc840030848c61665 0x03f01fc7f8fe3c42 0xf870001808e71e67

def z1084 : W := mkw 0x0000000000000080 0x0301a0e090000000 0xfc00000000000124 0x0383e381f0000000

def z1085 : W := mkw 0x922a569901536cf4 0xc3fffdffb1b8587c 0xfc001ff800c03bfc 0xa7fffffff0f81c78

def z1086 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0x000ffff8003ff8c9 0x87fc03fe07f803f8

def z1087 : W := mkw 0x830e9525240000f4 0x23ddf9ffb3396800 0xfc0fe0380700008d 0x038ce3fff718e000

def z1088 : W := mkw 0x7cf12a42dabe930b 0xd80002004cc697e7 0x03f01fc7f8fffc02 0xf800000008e71fe7

def z1089 : W := mkw 0x038c992624000010 0x21f72508236b2400 0x0ff0e1c038000104 0x03f303807fe70000

def z1090 : W := mkw 0xf957240dd36ecf6b 0xd0085a154e15fbd7 0x03fffe3ffffffc53 0xfc0c1c1e0f1fffff

def z1091 : W := mkw 0x54b00a42889a130a 0xc862070868c61665 0x03f01fc7f8fe3c02 0xf870000008e71e67

def z1092 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc00000000000174 0x03ffff9ff0000000

def z1093 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0x03f0fff8003ff948 0x87fc03fe0ff803f8

def z1094 : W := mkw 0x7df52a46dabe938b 0xdb01a2e0dec7b7e7 0x03ffffc7fffffc83 0xfb80e0600fe7ffe7

def z1095 : W := mkw 0x9002040901424c74 0xc0fe5d1f20105854 0xfc001e3fc0fe3f7e 0xfc7f1f9ff0181e7f

def z1096 : W := mkw 0x0000000000000014 0x036325aa30000000 0x0c00000000000004 0x0003038070000000

def z1097 : W := mkw 0x82081000000000e4 0x02d491ffb1280000 0xfffffff8000003cf 0x83fc03fffff80000

def z1098 : W := mkw 0xd4b00a42889a137e 0xc8fe5f1f68c61665 0x03f01fc7f8fe3c52 0xf87c1c1e08e71e67

def z1099 : W := mkw 0xb000000841464cf5 0xc3f7b5ffb0009156 0xfc000000003ffd0c 0x1ff303fff00003ff

def z1100 : W := mkw 0x74b00a4ac9de5f0b 0xc800020048c69777 0x03f01fc7f8fffc02 0xfc00000008e71fff

def z1101 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xfff001c7f8fe3d3c 0x78731f99f8e71e67

def z1102 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc000000003ffbfc 0x07fffffff00003f8

def z1103 : W := mkw 0x56d958d288ab3060 0xcab614b3656e14cd 0xfc0fe03ff8c1c4b5 0x7f8f1c67f71f1d9f

def z1104 : W := mkw 0x0000000000000094 0x0395a0e290000000 0xfc000000000003ac 0x0383e3e1f0000000

def z1105 : W := mkw 0x80200200001000f4 0x03fffdffb0800020 0xfc001fc000003bfc 0x83fffffff0e00060

def z1106 : W := mkw 0x0000000000000014 0x0163250830000000 0x0c00000000000104 0x0073038070000000

def z1107 : W := mkw 0x81848926240000f4 0x23fffdffb2432400 0xfc000000380003fc 0x03fffffff0070000

def z1108 : W := mkw 0x828a9d23240000f4 0x23fffdffb17a4c00 0xfffffff800c003ff 0xa3fffffffff81c00

def z1109 : W := mkw 0x2841200052248081 0x1301a0e094008182 0xfc0000000001c3ac 0x0383e3e1f0000180

def z1110 : W := mkw 0x403002008018030a 0x0000020048840221 0x03f01fc7f83e3c02 0xd800000008e70267

def z1111 : W := mkw 0x69552004d22c830b 0x110122004e05a383 0xffffe007ff3fc7af 0x5b83e381ff07e387

def z1112 : W := mkw 0x830e9525240000f4 0x23fffdffb3396800 0xfc0ffe3fc7c003ff 0xe3fffffff718fc00

def z1113 : W := mkw 0x80800802000000f4 0x03fffdffb0420400 0xfc001fc000c003fc 0xa3fffffff0e01c00

def z1114 : W := mkw 0x16aa9f632c921070 0xe9ff7d1921fa5c64 0xfc001ff800c03bfc 0xa3ffff99f0f81c60

def z1115 : W := mkw 0x80000000000000e0 0x02feddffa0000000 0xfc000000000003fc 0x03fffffff0000000

def z1116 : W := mkw 0x44b00a428898130a 0x0822060048c60621 0x03f001c038000100 0x0073000008e70000

def z1117 : W := mkw 0x0000000000000060 0x0062151920000000 0xfc001e07c0c0037e 0xe0731f99f0001c00

def z1118 : W := mkw 0x74b00a42c89e130b 0xc800020048c69767 0x03ff1fc7fffffc03 0xf800000008e7ffe7

def z1119 : W := mkw 0x80000000000000e4 0x0301b0f5b0000000 0xfc000000000003ac 0x0383e3e1f0000000

def z1120 : W := mkw 0x56f95ad288bb336a 0xc8f6171b6dee16ed 0x03fffffff8fffc53 0xfc7c1c1e0fff1fff

def z1121 : W := mkw 0x80000000000000e0 0x0301b0f590000000 0xfc000000000003ac 0x0383e3fff0000000

def z1122 : W := mkw 0x0000000000000074 0x03f735bb30000000 0xfc000000000003fc 0x03ff1ffff0000000

def z1123 : W := mkw 0x94200240089210f4 0xcbfffdffb0801064 0xfc00000000003bfc 0x03fffffff0000060

def z1124 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xffff1fc7fffe3fff 0xf873ff99f8e7fe67

def z1125 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x03ffffffffc003fb 0xe3fffc7e0ffffc00

def z1126 : W := mkw 0x0000000000000004 0x026205aa30000000 0x0c00000000000104 0x0073038070000000

def z1127 : W := mkw 0x0000000000000060 0x0062151920000000 0xfc0f1e38003ffbff 0x847f1ffff01803f8

def z1128 : W := mkw 0x0000000000000000 0x0022040000000000 0xfc0000000000037c 0x00731f81f0000000

def z1129 : W := mkw 0x0000000000000000 0x020000a000000000 0xfc000000000003ac 0x038303e1f0000000

def z1130 : W := mkw 0x00000000000000e0 0x03f7b5fbb0000000 0xfc000000000003fc 0x03fffffff0000000

def z1131 : W := mkw 0x80000000000000f4 0x016bfd5db0000000 0xfc0000000000003c 0x0003ff99f0000000

def z1132 : W := mkw 0x4bddb926b628830a 0x300002004f6f2681 0x03f0e1c038000000 0x000000000fe70000

def z1133 : W := mkw 0x81060405000000e0 0x0309f8f592116800 0xfffffe3fffc003ff 0xe38fffffff1ffc00

def z1134 : W := mkw 0x0002040100000060 0x006a5d1920104800 0xfc0f1e3fc7c003ff 0xe07fff99f018fc00

def z1135 : W := mkw 0x0000000000000080 0x0301a0e090000000 0xfc000007c03e07ae 0x5b83e3e1f0000207

def z1136 : W := mkw 0x0000000000000090 0x03ffedea90000000 0xfc000000000003fc 0x03fffffff0000000

def z1137 : W := mkw 0x54f10a4288ba136a 0xc86217196cc616e5 0xffffffc7f8ffff7f 0xf8731f99ffe71fe7

def z1138 : W := mkw 0x56b85ad2889b330a 0xc800020049ee166d 0x03f01ffff8fe3c02 0xfc00000008ff1e7f

def z1139 : W := mkw 0x80000000000000e0 0x0048d95da0000000 0xfc000000000002fc 0x000cfffff0000000

def z1140 : W := mkw 0x838e9d27240000f4 0x23fffdffb37b6c00 0xfff0fff838c003fc 0xa3ffffffffff1c00

def z1141 : W := mkw 0x1002040100020060 0xc008581100105844 0xf00f1e3fc7fffefb 0xfc0cfc7f8018ffff

def z1142 : W := mkw 0x439e9d27a408031a 0x21bf6e004b7f6e01 0x03fffffffffe07f3 0xfbfffc000ffffe07

def z1143 : W := mkw 0x409008028008030a 0x0022060048460601 0x03f01fc7f8fe0772 0xf8731c0008e71e07

def z1144 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x03ffffffffffc3fb 0xe3fffc600fffff80

def z1145 : W := mkw 0x69752204d23c838b 0x1301a2e0de85a3a3 0xffffffc7ff3fffaf 0xdb83e3e1ffe7e3e7

def z1146 : W := mkw 0x0000000000000010 0x01ff6d0820000000 0x0c000000000003f4 0x03ffff8070000000

def z1147 : W := mkw 0x82081000000000f4 0x03fffdffb1280000 0xfff0e1c0000003fc 0x03ffffffffe00000

def z1148 : W := mkw 0x0000000000000060 0x024011bb20000000 0xfc0000000000000c 0x000003fff0000000

def z1149 : W := mkw 0x0000000000000080 0x03d5a1ea90000000 0xfc000000000003ac 0x03f3e3e1f0000000

def z1150 : W := mkw 0xe957240dd36ccf8b 0x1008ca44ce15eb93 0x03ffe03fff3fc483 0x5c0ce0660f1fe39f

def z1151 : W := mkw 0x0000000000000070 0x016b7d1920000000 0xfc0000000000037c 0x0073ff99f0000000

def z1152 : W := mkw 0x6b7d7294d23da38b 0x1395a2e2dfada3ab 0x03ffffffff3ffc83 0xdf8ce0660fffe3ff

def z1153 : W := mkw 0x54900842888a130a 0xc800020048461645 0x03f00007f8fe0402 0x7800000008071e07

def z1154 : W := mkw 0x69572405d22c830b 0x100002004e15eb83 0x03fffe3fffffc403 0xf80000000f1fff87

def z1155 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x03fffff83fc001d1 0xa3fffc000ffffc00

def z1156 : W := mkw 0x0000000000000014 0x00f6050a20000000 0x0c00000000000104 0x0073038070000000

def z1157 : W := mkw 0x20000000400400e1 0x00629559a0008102 0xfc0f0007c73fc7ff 0x5873fff9f000e387

def z1158 : W := mkw 0x54b00a42889a130a 0xc800020048c61665 0x03ff1ffff8fffecb 0xfc0c007e08ff1fff

def z1159 : W := mkw 0xb002040941464ce5 0xc349f9ffb010d956 0xfc0f1e3fc7ffffff 0xff8ffffff018ffff

def z1160 : W := mkw 0x0000000000000000 0x0000000000000000 0xfff00007f800032e 0x40030381f8070000

def z1161 : W := mkw 0x80000000000000f4 0x02dcd9ffb0000000 0xfc0000000000000c 0x000c03fff0000000

def z1162 : W := mkw 0x80000000000000f4 0x00fedd5fa0000000 0xfc000000000003fc 0x007ffffff0000000

def z1163 : W := mkw 0x9000000801424ce4 0xc24091ffb0001054 0xfc0000000000380c 0x040003fff0000078

def z1164 : W := mkw 0x30000000400600e1 0xc363b5f9b0009146 0xfc0f1e07c7ffffff 0xfbf3fff9f000ffe7

def z1165 : W := mkw 0xd4b00a42889a13ea 0xc808da55c8c61665 0xf3f01fc7f8fe3efa 0xf80cfc7f88e71e67

def z1166 : W := mkw 0x14a00a4208921060 0xc862151920c21464 0x0c001fc000c03954 0xa0731f9870e01c60

def z1167 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0x0c000000000001d4 0x03fffffe70000000

def z1168 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xffff1ffff8fe3fff 0xf87f1f99f8ff1e67

def z1169 : W := mkw 0x82881802000000f4 0x03fffdffb16a0400 0xfffffffff8c003ff 0xe3ffffffffff1c00

def z1170 : W := mkw 0x8000000000000094 0x03ffedeeb0000000 0x0c00000000000104 0x03f3e38070000000

def z1171 : W := mkw 0x80000000000000f4 0x026addffb0000000 0xfc0000000000001c 0x00001ffff0000000

def z1172 : W := mkw 0x69552004d22c838b 0x10008240ce05a383 0xf3ffe007ff3fc423 0x5800e0018f07e387

def z1173 : W := mkw 0x80000000000000f4 0x03f7b5ffb0000000 0xfc0000000000037c 0x03f31ffff0000000

def z1174 : W := mkw 0x928a9d2b25424c74 0xe0fe5d1f217a5c54 0x00001ff800c03850 0xa47c1c1e00f81c78

def z1175 : W := mkw 0x80000000000000e4 0x02d491ffb0000000 0xfc0000000000004c 0x007c03fff0000000

def z1176 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xffffe007ff3fc7ef 0x5b8fe3ffff07e387

def z1177 : W := mkw 0x81840806000000f4 0x03fffdffb2432400 0xffffffc7ffc003ff 0xe3ffffffffe7fc00

def z1178 : W := mkw 0xd4b00a42889a139e 0xcb9deae6d8c61665 0x03f01fc7f8fe3c82 0xfb8ce06608e71e67

def z1179 : W := mkw 0x038e9d2724000014 0x23ff6daa337b6c00 0x0fffffffffc003ff 0xe3fffffe7ffffc00

def z1180 : W := mkw 0x8000000000000014 0x03ff6dae30000000 0x0c00000000000104 0x03ff038670000000

def z1181 : W := mkw 0x038e9d2724000010 0x23bf6ca0137b6c00 0x0fffffffffc003f7 0xe3ffff807ffffc00

def z1182 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc001e3800003bfc 0x87fffffff0180078

def z1183 : W := mkw 0x54b00a42889a130a 0xc800020048c61665 0x03f01fc7f8fe3e4a 0xf800001808e71e67

def z1184 : W := mkw 0x80000000000000f4 0x02feddffb0000000 0xfc000000000002fc 0x007cfffff0000000

def z1185 : W := mkw 0x8000000000000064 0x0040111f20000000 0xfc0000000000000c 0x0000039ff0000000

def z1186 : W := mkw 0xa000000841444ce5 0x024091ffb0008112 0xfc0000000001c00c 0x040003fff0000198

def z1187 : W := mkw 0x01868d2724000014 0x23ff6daa32536c00 0x0c000007ffc00134 0x63f3ff807007fc00

def z1188 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc001e00003e3bfe 0x83fffffff0000260

def z1189 : W := mkw 0xb002040941464cf5 0xc32bfcf5b010d956 0xfc0f1e3fc7ffffff 0xff8ffffff018ffff

def z1190 : W := mkw 0x838e9d2f25404c10 0x21bf6c04037b6c10 0x03ffffffffc003f3 0xe7fffc060ffffc18

def z1191 : W := mkw 0xa002040941444cf5 0x03fffdffb010c912 0xfc000000070003fc 0x03fffffff000e000

def z1192 : W := mkw 0x54b00a42889a130a 0xc800020048c61665 0x03f01fc7f8fe3f22 0xf803000008e71e67

def z1193 : W := mkw 0x838e9d2724000094 0x23ffedeeb37b6c00 0x0fffe1f83f000185 0x03ffe3e67fffe000

def z1194 : W := mkw 0x409008028008036a 0x0062171968460601 0xfff01fc7f8fe077e 0xf8731f99f8e71e07

def z1195 : W := mkw 0x69552004d22c830b 0x100002004e05a383 0x03f0e000383fc400 0x180000000f070387

def z1196 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x03ffffffffc1c3f3 0xe7fffc660ffffd98

def z1197 : W := mkw 0x0000000000000080 0x0301a0e090000000 0xfc0f1e38003ffbef 0x878fe3fff01803f8

def z1198 : W := mkw 0x0000000000000014 0x03f725aa30000000 0x0c000000000003a4 0x03f3e38070000000

def z1199 : W := mkw 0x0000000000000070 0x00fe5d1920000000 0xfc0000000000037c 0x007f1f99f0000000

def z1200 : W := mkw 0x0000000000000060 0x0062151920000000 0xfff01fc00000037e 0x80731f99f8e00000

def z1201 : W := mkw 0x0000000000000080 0x024081ea90000000 0xfc0000000000000c 0x000003fff0000000

def z1202 : W := mkw 0x00000000000000e0 0x0163b559b0000000 0xfc0000000000037c 0x0073ff99f0000000

def z1203 : W := mkw 0x69552004d22c838b 0x120082e0de05a383 0x03ffe007ff3fc403 0x580000600f07e387

def z1204 : W := mkw 0x68512000d22c830b 0x100002004c048383 0x03f00007f83fc402 0x5800000008070387

def z1205 : W := mkw 0x54b00a42889a130a 0xc800020048c61665 0x00001fc000fe3c00 0xb800000000e01e67

def z1206 : W := mkw 0x00000000000000e0 0x026295f9b0000000 0xfc0000000000037c 0x00731ff9f0000000

def z1207 : W := mkw 0x8000000000000094 0x039de8e690000000 0xfc0000000000008c 0x038ce3e7f0000000

def z1208 : W := mkw 0x938e9d27240200f4 0xe3fffdffb37b7c44 0xfffffffffffe3fff 0xfbfffffffffffe67

def z1209 : W := mkw 0x94a20e4b09d25cf4 0xcbfffdffb0d25c74 0xfc001ff800c03bfc 0xa7fffffff0f81c78

def z1210 : W := mkw 0x0208100000000014 0x03f725aa31280000 0x0ffffff8000003c7 0x83ff03807ff80000

def z1211 : W := mkw 0x80414090002120e4 0x024091ffb4000088 0xfc0000000001c00c 0x040003fff0000198

def z1212 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xffffe0003f3fc58d 0x1b83e3e1ff07e387

def z1213 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc001e07c0c003fe 0xe3fffffff0001c00

def z1214 : W := mkw 0x00000000000000e0 0x0341b1f9b0000000 0xfc000000000003ac 0x0383e3f9f0000000

def z1215 : W := mkw 0x411400048008038a 0x0301a2e0da052201 0xffffe007ff3e07af 0x5b83e3e1ff07e207

def z1216 : W := mkw 0x938e9d2f25424cf4 0xe3fffdffb37b7c54 0xffffffffffc03bff 0xe7fffffffffffc78

def z1217 : W := mkw 0x82081000000000f4 0x03fffdffb1280000 0xfffffff8003ffbff 0x87fffffffff803f8

def z1218 : W := mkw 0x038c992624000010 0x23b724a0136b2400 0x0ff0e1c038000104 0x03f303807fe70000

def z1219 : W := mkw 0x0000000000000004 0x034121aa30000000 0x0c00000000000104 0x0383038070000000

def z1220 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0xf3fffe3fc7fffffb 0xff8cfc7f8f18ffff

def z1221 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xfff0e007ff3fc52c 0x5b83e3e1ff07e387

def z1222 : W := mkw 0x69552004d22c838b 0x1101a240de05a383 0x03ffe007ff3fc403 0x5800e0000f07e387

def z1223 : W := mkw 0x838c9926240000f4 0x23fffdffb36b2400 0xfffffff8380003ff 0x83ffffffffff0000

def z1224 : W := mkw 0x80000000000000e4 0x0341b1ffb0000000 0xfc0000000000010c 0x038303fff0000000

def z1225 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x03f0ffffffc00170 0xe3fffc000ffffc00

def z1226 : W := mkw 0xb000000841464ce5 0xc26295ffb0009156 0xfc001e07c0ffff7e 0xfc731ffff0001fff

def z1227 : W := mkw 0x56ba9f63ac9a131a 0xe8be4e0049fe5e65 0x03f01ffff8fe3c52 0xf87c1c0008ff1e67

def z1228 : W := mkw 0x82285290001120f4 0x03fffdffb1a80028 0xfc0f1ff8003ffbff 0x87fffffff0f803f8

def z1229 : W := mkw 0x838e9d27240000f4 0x23fffdffb37b6c00 0xfc001fffffc003fc 0xe3fffffff0fffc00

def z1230 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xffffe000000003ff 0x03ffffffff000000

def z1231 : W := mkw 0x80000000000000e4 0x03d5b1ffb0000000 0xfc000000000003ec 0x03ffe3fff0000000

def z1232 : W := mkw 0xa0000000400400f5 0x03fffdffb0008102 0xfc000007c70007fc 0x5bfffffff000e007

def z1233 : W := mkw 0xa9452004522480e5 0x1341b1ffb601a182 0xfc0fe0000701c08d 0x0380e3fff700e180

def z1234 : W := mkw 0x80000000000000f4 0x012bfc55b0000000 0xfc0000000000033c 0x0003ff81f0000000

def z1235 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xf3ffe007ff3fc6ab 0x5b80e0618f07e387

def z1236 : W := mkw 0x028a1c0300000000 0x00be4c00017a4c00 0x03ffffffffc003f3 0xe3fffc000ffffc00

def z1237 : W := mkw 0x0080080200000080 0x0323a4e090420400 0xfff01fc7f8c003fe 0xe3f3ffe1f8e71c00

def z1238 : W := mkw 0x0000000000000060 0x0062151920000000 0xfc0000000000005c 0x00701f99f0000000

def z1239 : W := mkw 0x01868d2724000010 0x212b6c0002536c00 0x03ffffc7ffc003f3 0xe3f3fc000fe7fc00

def z1240 : W := mkw 0x80000000000000e0 0x006add5da0000000 0xfc0000000000037c 0x0073ff99f0000000

def z1241 : W := mkw 0x80000000000000f4 0x039df8f790000000 0xfc000000000003fc 0x038ffffff0000000

def z1242 : W := mkw 0x69552004d22c830b 0x100002004e05a383 0x03ffe0003f01c001 0x000000000f07e180

def z1243 : W := mkw 0x5df52a469aba930a 0xd80002004ec736e5 0x03f0ffc7f8fe3c02 0xf80000000fe71e67

def z1244 : W := mkw 0x0000000000000010 0x01f7250820000000 0x0c00000000000104 0x03f3038070000000

def z1245 : W := mkw 0xa38e9d27640400f5 0x23fffdffb37bed02 0xffffffffffffc7ff 0xfbffffffffffff87

def z1246 : W := mkw 0x04a00a4208901060 0x0862151920c20420 0xfc0001c00000037c 0x00731f99f0e00000

def z1247 : W := mkw 0xa38e9d2f65444cf5 0x23fffdffb37bed12 0xffffffffffc1c3ff 0xe7fffffffffffd98

def z1248 : W := mkw 0x0000000000000074 0x00f6151b20000000 0xfc0000000000037c 0x00731f99f0000000

def z1249 : W := mkw 0x94a00a42089210f4 0xcbfffdffb0c21464 0xfc001fc7c0fe3ffe 0xfbfffffff0e01e67

def z1250 : W := mkw 0x0000000000000080 0x0309e8e090000000 0xfc000000000003fc 0x038fffe1f0000000

def z1251 : W := mkw 0x8000000000000060 0x006a5d1d20000000 0xfc0000000000037c 0x007f1f9ff0000000

def z1252 : W := mkw 0x82085090000120f4 0x03fffdffb1280008 0xfc000038000003fc 0x07fffffff0180018

def z1253 : W := mkw 0x0000000000000014 0x03f725aa30000000 0x0c00000000000144 0x03ff039e70000000

def z1254 : W := mkw 0x8000000000000074 0x00fe5d1f20000000 0xfc0000000000005c 0x007c1f9ff0000000

def z1255 : W := mkw 0xfd962c4fdbcedce1 0xd92bfc55f257fd57 0xfc000007ffc00434 0x7803fc01f007fc07

def z1256 : W := mkw 0x0000000000000014 0x03ff6daa30000000 0x0c000000000003fc 0x03fffffe70000000

def z1257 : W := mkw 0x8002040901404cf4 0x03fffdffb0104810 0xfc000038000003fc 0x07fffffff0180018

def z1258 : W := mkw 0x50100000800a036a 0xc000121148041245 0xf3f01e07f8fe3e7a 0xf8001c1988071e67

def z1259 : W := mkw 0x0000000000000080 0x0301a0e090000000 0xfc0000000000002c 0x0003e3e1f0000000

def z1260 : W := mkw 0xa002040941444cf5 0x03fffdffb010c912 0xfc0f1e38073ffbff 0x87fffffff018e3f8

def z1261 : W := mkw 0x427952908039230a 0x02d403aa4dac02a9 0xfffffff8003fffcf 0x9ffc03fffff803ff

def z1262 : W := mkw 0x2945200452248081 0x1301a0e09601a182 0xfc0fe007c73fc7af 0x5b83e3e1f700e387

def z1263 : W := mkw 0x83cfddb7242120f4 0x23fffdffb77b6c88 0xffffffffffc1c3ff 0xe7fffffffffffd98

def z1264 : W := mkw 0xb002040941464cf5 0xc3fffdffb010d956 0xfc000007c7c00534 0x7bf3ff81f000fc07

def z1265 : W := mkw 0x80800802000000e4 0x026295ffb0420400 0xfff01fc7f8c0037e 0xe0731ffff8e71c00

def z1266 : W := mkw 0x54900842888a1060 0xc862151960461445 0xfff01fc7f8c0077e 0xf8731f99f8e71c07

def z1267 : W := mkw 0xa947240d5364cce1 0x1309f8f59611e992 0xfc0fe0380701c3fd 0x078ffffff718e198

def z1268 : W := mkw 0x0000000000000000 0x02f605aa20000000 0x0c00000000000104 0x03f3038070000000

def z1269 : W := mkw 0x1000000000020060 0xc2f615bb20001044 0xfc0f1e3fc0ffffff 0xffff1ffff0181fff

def z1270 : W := mkw 0x81040004000000f4 0x03fffdffb2012000 0xfff0e000380003fc 0x03ffffffff070000

def z1271 : W := mkw 0x038e9d2724000060 0x20621519237b6c00 0xffffffffffc0037f 0xe0731f99fffffc00

def z1272 : W := mkw 0xa002040941444c81 0x0309e8e49010c912 0xfc0f00380701c3ad 0x078fe3e7f018e198

def z1273 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xfffffe07ffffc7ff 0xfb83ffe1ff07ff87

def z1274 : W := mkw 0x0104000400000080 0x0301a0e092012000 0xfc0fe000070003ad 0x0383e3e1f700e000

def z1275 : W := mkw 0x9000000801424cf4 0xc3fffdffb0001054 0xfc00000000003bfc 0x07fffffff0000078

def z1276 : W := mkw 0xf4b20e4bc9de5f8b 0xc808ca44c8d6df77 0x03ff1ffffffffc83 0xfc0ce06608ffffff

def z1277 : W := mkw 0x0208100000000014 0x03f725aa31280000 0x0ff0e1c000000104 0x03f303807fe00000

def z1278 : W := mkw 0x69552004d22c8081 0x1301a0e0d605a183 0xfc0fe007ff01c7ad 0x5b83e3e1f707e187

def z1279 : W := mkw 0x80020401000000f4 0x03fffdffb0104800 0xfc0f0038070003fd 0x03fffffff018e000

def z1280 : W := mkw 0x0041000000200080 0x0301a0e094000080 0xfc0fe0000001c3ad 0x0383e3e1f7000180

def z1281 : W := mkw 0x00000000000000e0 0x0323b4f1b0000000 0xfc000000000003bc 0x0383ffe1f0000000

def z1282 : W := mkw 0x820a9521240000f4 0x23fffdffb1384800 0xfc000038000003fc 0x03fffffff0180000

def z1283 : W := mkw 0x80000000000000e4 0x024091ffb0000000 0xfc0000000000027c 0x00001ffff0000000

def z1284 : W := mkw 0x81068525240000f4 0x23fffdffb2116800 0xfc000000070003fc 0x03fffffff000e000

def z1285 : W := mkw 0x0000000000000090 0x032bece090000000 0xfc000000000003bc 0x0383ffe1f0000000

def z1286 : W := mkw 0x69552004d22c830b 0x120002a04e05a383 0x03ffe007ff3fc483 0x5b8000600f07e387

def z1287 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xfff01fc7f8fe3ffe 0xf87f1ffff8e71e67

def z1288 : W := mkw 0x54300240889a136a 0xc840131968841265 0x00000000003e3c00 0x1800001800000267

def z1289 : W := mkw 0xf4b00a4ac9de5feb 0xc8009255c8c69777 0xf3f01fc7f8fffc0a 0xfc00007f88e71fff

def z1290 : W := mkw 0x0000000000000060 0x0062151920000000 0xfc000007c03e077e 0x58731f99f0000207

def z1291 : W := mkw 0x56b85ad2889b330a 0xc8d4030a49ee166d 0x03f01ffff8fe3c42 0xfc7c001e08ff1e7f

def z1292 : W := mkw 0x0080080200000014 0x03f725aa30420400 0x0ff001c038000104 0x03f3038078e70000

def z1293 : W := mkw 0x0249509000212000 0x029400a205280088 0x03fffff8003ffbcb 0x87fc007e0ff803f8

def z1294 : W := mkw 0x01840806000000e0 0x0363b5f9b2432400 0xffffffc7ffc003ff 0xe3f3fff9ffe7fc00

def z1295 : W := mkw 0x0000000000000084 0x024081eab0000000 0xfc0000000000000c 0x000003e1f0000000

def z1296 : W := mkw 0x69552004d22c830b 0x100002004e05a383 0x00000007ff3fc400 0x580000000007e387

def z1297 : W := mkw 0x2b4d70945225a081 0x13d5a1ea9729a18a 0xfc0fe0380701c3ed 0x07ffe3fff718e198

def z1298 : W := mkw 0xa0000000400400f5 0x03fffdffb0008102 0xfc0f1e3fc73fffff 0xdffffffff018e3ff

def z1299 : W := mkw 0x94a00a42089210e4 0xca6295ffb0c21464 0xfc001fc000c0385c 0xa0701ffff0e01c60

def z1300 : W := mkw 0x46f95ad288b9330a 0x080002004dee06a9 0x03fffff8383ff803 0x840000000fff03f8

def z1301 : W := mkw 0x56b81a42889a130a 0xc800020049ee1665 0x03fffffff8fe3c03 0xf80000000fff1e67

def z1302 : W := mkw 0xb002040941464cf1 0xc1fffd5da010d956 0xfc0f1e3fc7ffffff 0xfffffffff018ffff

def z1303 : W := mkw 0x69552004d22c830b 0x110122004e05a383 0x03ffe007ff3fc483 0x5b80e0000f07e387

def z1304 : W := mkw 0xf4b20e4bc9de5feb 0xc82ade55c8d6df77 0xf3ff1ffffffffffb 0xfc7ffc7f88ffffff

def z1305 : W := mkw 0xa002040941444ce5 0x0248d9ffb010c912 0xfc0f00380701c08d 0x040ce3fff018e198

def z1306 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc000007c03e07fe 0x5bfffffff0000207

def z1307 : W := mkw 0x0000000000000080 0x0395a0e090000000 0xfc000000000003ec 0x03ffe3e1f0000000

def z1308 : W := mkw 0x68716290d23da30b 0x100002004c8483ab 0x00000000003ffc00 0x1c000000000003ff

def z1309 : W := mkw 0x57be9f67ac9a137a 0xe8fe5f196bff7e65 0x03fffffffffe3c53 0xf87c1c180ffffe67

def z1310 : W := mkw 0x6bddb926f62c831b 0x31b726004f6fa783 0x03ffe1c7ff3fc503 0x5bf300000fe7e387

def z1311 : W := mkw 0xfc712248dbfedfeb 0xda4093fdfc8493f7 0xfc000000003ffc0c 0x1c0003fff00003ff

def z1312 : W := mkw 0x80020401000000f4 0x03fffdffb0104800 0xfc0f1e3fc7fffbff 0xe7fffffff018fff8

def z1313 : W := mkw 0x0249509000212060 0x02f615bb25280088 0xfc0fe0380001c3fd 0x07ff1ffff7180198

def z1314 : W := mkw 0x80000000000000e4 0x020090f5b0000000 0xfc0000000000000c 0x000003e1f0000000

def z1315 : W := mkw 0x0000000000000060 0x0062151920000000 0xfc001e00003e3b7e 0x80731f99f0000260

def z1316 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0x03ffe007ff3fc7a3 0x5b83e0600f07e387

def z1317 : W := mkw 0x54b00a42889a136a 0xc840131968c61665 0x03f01fc7f8fe3c02 0xf800001808e71e67

def z1318 : W := mkw 0x80000000000000e0 0x020090f590000000 0xfc0000000000000c 0x000003fff0000000

def z1319 : W := mkw 0x29452004522480e1 0x1363b5f9b601a182 0xfc0fe0000701c3fd 0x03f3fff9f700e180

def z1320 : W := mkw 0x8000000000000074 0x01ff7d1f20000000 0xfc000000000003fc 0x03ffff9ff0000000

def z1321 : W := mkw 0xa000000841444cf5 0x03fffdffb0008112 0xfc0000000001c3fc 0x07fffffff0000198

def z1322 : W := mkw 0x55b40a46889a130a 0xc90122004ac73665 0x03ffffc7fffe3fa3 0xfb83e0000fe7fe67

def z1323 : W := mkw 0x04a00a4208901000 0x0862050820c20420 0x0c0001c000000104 0x0073038070e00000

def z1324 : W := mkw 0x0000000000000074 0x03f735bb30000000 0xfc00000000000134 0x03f31f81f0000000

def z1325 : W := mkw 0x81868d27240000f4 0x23fffdffb2536c00 0xfc0f1e3fffc003ff 0xe3fffffff01ffc00

def z1326 : W := mkw 0x56b81a42889a130a 0xc894020049ee1665 0x03fffffff8fe3fc3 0xfbfc00000fff1e67

def z1327 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xfff01fc7f8ffff7e 0xfc731ffff8e71fff

def z1328 : W := mkw 0xb000000841464ce5 0xc341b1ffb0009156 0xfc0f0007c73fffaf 0x5f83e3fff000e3ff

def z1329 : W := mkw 0x54b00a42889a136a 0xc822161148c61665 0xf3f01fc7f8fe3f7a 0xf8731c1988e71e67

def z1330 : W := mkw 0x54300240889a130a 0xc800020048841265 0x00001e07c0fe3c02 0xf800000000001e67

def z1331 : W := mkw 0xb002040941464cf5 0xc36bfdffb010d956 0xfc0f1e3fc7fffeff 0xfc0ffffff018ffff

def z1332 : W := mkw 0xb002040941464cf5 0xc32bfcf5b010d956 0xfc0f0007c7ffc7bf 0x7b83ffe1f000ff87

def z1333 : W := mkw 0x0000000000000000 0x02f605aa20000000 0x0c000000000003cc 0x03ff03fe70000000

def z1334 : W := mkw 0x54b00a42889a130a 0xc800020048c61665 0xf3f01fc7f8fe3e2a 0xf800000188e71e67

def z1335 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc0f0007c70003ff 0x43fffffff000e000

def z1336 : W := mkw 0x50100000800a030a 0xc000020048041245 0x03f01e07f8fe3c02 0xf800000008071e67

def z1337 : W := mkw 0x80414090002120f4 0x03fffdffb4000088 0xfc0000000001c3fc 0x07fffffff0000198

def z1338 : W := mkw 0xb002040941464ce1 0xc2feddffa010d956 0xfc0f1e3fc7ffffff 0xfffffffff018ffff

def z1339 : W := mkw 0x0000000000000080 0x0301a0e090000000 0xfc0000000000008c 0x0380e3e1f0000000

def z1340 : W := mkw 0xb0820c0b41464cf5 0xc3fffdffb052dd56 0xffff1fffffffffff 0xfffffffff8ffffff

def z1341 : W := mkw 0xb002040941464cf5 0xc16bfd5db010d956 0xfc0f1e3fc7ffffff 0xfc7ffffff018ffff

def z1342 : W := mkw 0xd4b00a4a89da5f6a 0xc862171d68c61675 0xfff01fc7f8fe3f7e 0xfc731f9ff8e71e7f

def z1343 : W := mkw 0xa0000000400400f5 0x03fffdffb0008102 0xfc0f00000701c3fd 0x03fffffff000e180

def z1344 : W := mkw 0x80000000000000f4 0x03bffcf7b0000000 0xfc000000000003bc 0x038fffe7f0000000

def z1345 : W := mkw 0x80000000000000f4 0x01fffd5fb0000000 0xfc0000000000037c 0x007fff9ff0000000

def z1346 : W := mkw 0x3002040941464c01 0xc00848000010d956 0x000f1e3fc7fffefb 0xfc0cfc7e0018ffff

def z1347 : W := mkw 0x8000000000000094 0x0309e8e490000000 0xfc000000000003ac 0x0383e3e1f0000000

def z1348 : W := mkw 0x82495090002120e4 0x02d491ffb5280088 0xfc0fe0380001c08d 0x078c03fff7180198

def z1349 : W := mkw 0x0000000000000090 0x03b7a4e090000000 0xfc000000000003ac 0x03f3e3e1f0000000

def z1350 : W := mkw 0x0000000000000000 0x0062050820000000 0xfc0000000000032c 0x00730381f0000000

def z1351 : W := mkw 0x2000000040040095 0x03f7a5eab0008102 0xfc0f0007c73fc7af 0x5bf3e3e1f000e387

def z1352 : W := mkw 0x0104000400000080 0x0301a0e092012000 0xfc000007ff0003ac 0x4383e3e1f007e000

def z1353 : W := mkw 0x8000000000000074 0x03f735bf30000000 0x0c00000000000104 0x03f3039e70000000

def z1354 : W := mkw 0x47be9f67ac98131a 0x29bf6e004bff6e21 0x03ffffffffc003f3 0xe3fffc000ffffc00

def z1355 : W := mkw 0x80000000000000f4 0x03d5b1ffb0000000 0xfc0000000000000c 0x038003fff0000000

def z1356 : W := mkw 0xab4fb52d7764cc91 0x339de8e49739e992 0x000fe0380701c081 0x078ce0660718e198

def z1357 : W := mkw 0x0000000000000080 0x0301a0e090000000 0xfc0000000000010c 0x038303e1f0000000

def z1358 : W := mkw 0xf8512008d36ecfeb 0xd0009255cc0493d7 0xf0000000003ffc08 0x1c00007f800003ff

def z1359 : W := mkw 0x00000000000000e0 0x00629559a0000000 0xfc000000000003fc 0x0073fff9f0000000

def z1360 : W := mkw 0x16a85ad208933060 0xcaf615bb21ea146c 0xfc001ff800c03bfc 0xa7ff1ffff0f81c78

def z1361 : W := mkw 0x80000000000000e4 0x024091ffb0000000 0xfc000000000002cc 0x000c03fff0000000

def z1362 : W := mkw 0xb002040941464ce5 0xc248d9ffb010d956 0xfc000007c7c0043c 0x7800fffff000fc07

def z1363 : W := mkw 0x8000000000000084 0x0301a0e690000000 0xfc000000000003ac 0x0383e3e7f0000000

def z1364 : W := mkw 0x830e9525240000f4 0x23fffdffb3396800 0xffffe03fff0003ff 0x43ffffffff1fe000

def z1365 : W := mkw 0x0000000000000014 0x03f725aa30000000 0x0c0000000000010c 0x03f303fe70000000

def z1366 : W := mkw 0xb002040941464cf5 0xc3fffdffb010d956 0xfc001e3fc7c03ffc 0xfffffffff018fc7f

def z1367 : W := mkw 0x80800802000000f4 0x03fffdffb0420400 0xfff001c0380003fc 0x03fffffff8e70000

def z1368 : W := mkw 0x038e9d2724000080 0x2301a0e0937b6c00 0xffffffffffc003af 0xe383e3e1fffffc00

def z1369 : W := mkw 0x0945200412208000 0x130120a016012080 0x0c00e00000000104 0x0383038077000000

def z1370 : W := mkw 0x69556094d22da38b 0x1301a2e2de05a38b 0xffffe007ff3fc7af 0x5f83e3e7ff07e39f

def z1371 : W := mkw 0x81040004000000f4 0x03fffdffb2012000 0xfc000007ff0003fc 0x43fffffff007e000

def z1372 : W := mkw 0x6bffffb7f63da31b 0x31bf6e004fffefab 0x03fffffffffffff3 0xfffffc000fffffff

def z1373 : W := mkw 0x838e9d27240000f4 0x23bffcf5b37b6c00 0xffffffffffc003ff 0xe3ffffe1fffffc00

def z1374 : W := mkw 0x820a1401000000f4 0x03fffdffb1384800 0xffffffffc7c003ff 0xe3fffffffff8fc00

def z1375 : W := mkw 0xb002040941464ce5 0xc26addffb010d956 0xfc0f1e3fc7ffffff 0xfc7ffffff018ffff

def z1376 : W := mkw 0x427952908039230a 0x000002004dac02a9 0x03fffffff83ffc03 0xdc0000000fff03ff

def z1377 : W := mkw 0x495520049228830a 0x100002004e052281 0x03f0e007f83e0402 0x580000000f070207

def z1378 : W := mkw 0xb000000841464ce1 0xc20090f590009156 0xfc000000003ffc0c 0x1c0003fff00003ff

def z1379 : W := mkw 0x838e9d27240000f0 0x23bffcf5937b6c00 0xffffffffffc003ff 0xe3fffffffffffc00

def z1380 : W := mkw 0xb002040941464ce1 0xc309f8f59010d956 0xfc000007c7c007bc 0x7b83ffe1f000fc07

def z1381 : W := mkw 0x54b00a42889a136a 0xc800121148c61665 0xf3f01fc7f8fe3c32 0xf8001c0188e71e67

def z1382 : W := mkw 0xfbdfbd2ff76ecfeb 0xf008da55cf7fffd7 0xf3fffffffffffefb 0xfc0cfc7f8fffffff

def z1383 : W := mkw 0x2000000040040081 0x03d5a1ea90008102 0xfc0f1e3fc73fffef 0xdfffe3fff018e3ff

def z1384 : W := mkw 0xb000000841464ce5 0xc24091ffb0009156 0xfc0000000000040c 0x180003fff0000007

def z1385 : W := mkw 0xa9452004522480f5 0x13fffdffb601a182 0xffffe007ff01c3ff 0x43ffffffff07e180

def z1386 : W := mkw 0x0000000000000074 0x03f735bb30000000 0x0c00000000000154 0x03f31f9870000000

def z1387 : W := mkw 0x0080080200000000 0x0062050820420400 0x0ff01fc7f8c00376 0xe0731f8078e71c00

def z1388 : W := mkw 0x0000000000000014 0x03f725aa30000000 0x0c000000000003c4 0x03ff038070000000

def z1389 : W := mkw 0xb002040941464cf5 0xc3fffdffb010d956 0xfc001e07c7fe3ffe 0xfbfffffff000fe67

def z1390 : W := mkw 0xfb7f769dd37fefeb 0xd008da55cfbdfbff 0xf3fffffffffffefb 0xfc0cfc7f8fffffff

def z1391 : W := mkw 0x69d52806d22c830b 0x102206004e47a783 0x03ffffc7ffffc773 0xf8731c000fe7ff87

def z1392 : W := mkw 0x6bdfbd27f62c839b 0x31bfee40cf7fef83 0xf3ffffffffffc7fb 0xfbfffc618fffff87

def z1393 : W := mkw 0x69756294d23da30b 0x100002004e85a3ab 0x03ffe007ff3ffc03 0x5c0000000f07e3ff

def z1394 : W := mkw 0x80000000000000f4 0x03f7b5ffb0000000 0xfc000000000003cc 0x03ff03fff0000000

def z1395 : W := mkw 0x94800842088210f4 0xcbfffdffb0421444 0xfc00000000c003fc 0x23fffffff0001c00

def z1396 : W := mkw 0x7df52a46dabe936b 0xd86217196ec7b7e7 0x03ffffc7fffffc53 0xf8701c180fe7ffe7

def z1397 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0xf00f003fc7fffcb9 0x7c0cfc7f8018ffff

def z1398 : W := mkw 0xb002040941464cf5 0xc3fffdffb010d956 0xfc0f1e3fc7c007ff 0xfbfffffff018fc07

def z1399 : W := mkw 0x69552004d22c830b 0x100002004e05a383 0x03ffe007ff3fc723 0x580300000f07e387

def z1400 : W := mkw 0xb000000841464cf5 0xc3fffdffb0009156 0xfc0f0007c73fffff 0x5ffffffff000e3ff

def z1401 : W := mkw 0x69572405d22c830b 0x10084a004e15eb83 0x03fffe3fffffc6f3 0xf80cfc000f1fff87

def z1402 : W := mkw 0xf6fb5edbc9ff7feb 0xc808da55cdfedfff 0xf3fffffffffffefb 0xfc0cfc7f8fffffff

def z1403 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xfff01fc7f8fe3d36 0xf8731f81f8e71e67

def z1404 : W := mkw 0x54b00a42889a130a 0xc822060048c61665 0x03f01fc7f8fe3d02 0xf873000008e71e67

def z1405 : W := mkw 0x0208100000000080 0x0395a0e091280000 0xfffffff8000003ef 0x83ffe3e1fff80000

def z1406 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc000000000003bc 0x03f3ffe1f0000000

def z1407 : W := mkw 0x7ffd7ad6dabfb30b 0xd80002004fefb7ef 0x03fffffffffffc03 0xfc0000000fffffff

def z1408 : W := mkw 0x038e9d2724000070 0x23ff7dbb237b6c00 0xffffffffffc003ff 0xe3fffffffffffc00

def z1409 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc0f00380001c3fd 0x07fffffff0180198

def z1410 : W := mkw 0xb002040941464cf5 0xc3ddf9ffb010d956 0xfc0f0038073ffc8d 0x1f8ce3fff018e3ff

def z1411 : W := mkw 0x6b7d7294d23da30b 0x10d4030a4fada3ab 0x03ffffffff3ffc43 0xdc7c001e0fffe3ff

def z1412 : W := mkw 0x0000000000000000 0x0062050820000000 0x0c0000000000034c 0x0073039870000000

def z1413 : W := mkw 0x54b00a42889a130a 0xc822060048c61665 0xfff01fc7f8fe3f7e 0xf8731f81f8e71e67

def z1414 : W := mkw 0x69552004d22c838b 0x1101a240ce05a383 0xf3ffe007ff3fc7ab 0x5b83e0618f07e387

def z1415 : W := mkw 0x0000000000000004 0x02d401aa30000000 0x0c000000000003cc 0x03fc03fe70000000

def z1416 : W := mkw 0x54b00a42889a130a 0xc800020048c61665 0x00000007f8fe3c00 0x7800000000071e67

def z1417 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc0f0000003fc3ff 0x03fffffff0000380

def z1418 : W := mkw 0x411400048008030a 0x010122004a052201 0x03ffe007ff3e07a3 0x5b83e0000f07e207

def z1419 : W := mkw 0x90000000000200e4 0xc24091ffb0001044 0xfc000000003e3c0c 0x180003fff0000267

def z1420 : W := mkw 0x80000000000000e4 0x024091ffb0000000 0xfc0000000000034c 0x007003fff0000000

def z1421 : W := mkw 0x80000000000000e4 0x0363b5ffb0000000 0xfc000000000003fc 0x03f3fffff0000000

def z1422 : W := mkw 0x0080080200000060 0x0062151920420400 0xfc001fc000c0037c 0xa0731f99f0e01c00

def z1423 : W := mkw 0x2945200452248095 0x13f7a5eab601a182 0x0c0fe0000701c185 0x03f3e3e07700e180

def z1424 : W := mkw 0x57be9f67ac9a137a 0xe9ff7f196bff7e65 0x03fffffffffe3ff3 0xfbfffc180ffffe67

def z1425 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0xf3ff1fffc7fffffb 0xfc7cfc7f88f8ffff

def z1426 : W := mkw 0x830e9525240000f4 0x23fffdffb3396800 0xfffffff8070003ff 0x83fffffffff8e000

def z1427 : W := mkw 0x0000000000000014 0x032324a030000000 0x0c00000000000104 0x0383038070000000

def z1428 : W := mkw 0x82081000000000f4 0x03fffdffb1280000 0xfc001ff8000003fc 0x83fffffff0f80000

def z1429 : W := mkw 0x80000000000000e4 0x0341b1ffb0000000 0xfc0000000000002c 0x0003e3fff0000000

def z1430 : W := mkw 0x94a00a42089210f4 0xcbfffdffb0c21464 0xfff01fc7f8c03bfe 0xe3fffffff8e71c60

def z1431 : W := mkw 0x0184892624000014 0x23f725aa32432400 0x0c00000038000104 0x03f3038070070000

def z1432 : W := mkw 0x80020401000000f4 0x03fffdffb0104800 0xfc001e3800c003fc 0xa3fffffff0181c00

def z1433 : W := mkw 0xb002040941464ce1 0xc208d8f59010d956 0xfc0f1e3fc7fffeff 0xfc0cfffff018ffff

def z1434 : W := mkw 0x6bddb926f62c830b 0x300002004f6fa783 0x03ffe1c7ff3fc403 0x580000000fe7e387

def z1435 : W := mkw 0x9002040901424c60 0xc06a5d1d20105854 0xfc001e3800c03b7c 0xa47f1f9ff0181c78

def z1436 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0x03ffe0003f01c081 0x0380e0600f07e180

def z1437 : W := mkw 0x69d7ad27f62c830b 0x300002004e57ef83 0x03ffe007ffffc403 0x780000000f07ff87

def z1438 : W := mkw 0x69756294d23da38b 0x1301a2e0de85a3ab 0xffffe007ff3fffaf 0x5f83e3e1ff07e3ff

def z1439 : W := mkw 0xb000000841464ce1 0xc301b0f590009156 0xfc000000003fffac 0x1f83e3fff00003ff

def z1440 : W := mkw 0x2b4ff5b57625a091 0x339de8e29739e98a 0x000fe0380701c081 0x078ce0660718e198

def z1441 : W := mkw 0x1002040100020070 0xc1ff7d1920105844 0xfc0f1e3fc7fe3fff 0xfbffff99f018fe67

def z1442 : W := mkw 0x0104000400000060 0x0163351922012000 0xffffe007ff0003ff 0x43f3ff99ff07e000

def z1443 : W := mkw 0x04a00a4208901014 0x0bf725aa30c20420 0x0c0001c000000104 0x03f3038070e00000

def z1444 : W := mkw 0x4b7d72949239a30a 0x100002004fad22a9 0x03fffff8383ff803 0x840000000fff03f8

def z1445 : W := mkw 0x038e9d2724000014 0x21bf6c00337b6c00 0x0fffffffffc003f7 0xe3fffc007ffffc00

def z1446 : W := mkw 0x80000000000000f4 0x03bffcf5b0000000 0xfc000000000003fc 0x03ffffe1f0000000

def z1447 : W := mkw 0x80000000000000f0 0x03bffcf590000000 0xfc000000000003fc 0x03fffffff0000000

def z1448 : W := mkw 0x6a797290d23da30b 0x100002004dac83ab 0x03fffff8003ffc03 0x9c0000000ff803ff

def z1449 : W := mkw 0x2000000040040081 0x020080e090008102 0xfc000000003fc40c 0x180003e1f0000387

def z1450 : W := mkw 0xb26b569941776feb 0xc2dcdbff8db8dbfe 0xf3f0e1c7c7c00530 0x7bf0ff818fe0fc07

def z1451 : W := mkw 0xf957240dd36ecfeb 0xd008da55ce15fbd7 0xf3ffe007ffffc433 0x7800fc018f07ff87

def z1452 : W := mkw 0x1420024008921060 0xc840111920801064 0xfc0000000000380c 0x00000399f0000060

def z1453 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c00000000000104 0x0003038070000000

def z1454 : W := mkw 0x90000000000200f4 0xc3fffdffb0001044 0xfc001e0000c03bfc 0xa3fffffff0001c60

def z1455 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x03fffffffffe3bfb 0xe3fffc180ffffe60

def z1456 : W := mkw 0x0288180200000060 0x02f615bb216a0400 0xfffffffff8c003ff 0xe3ff1fffffff1c00

def z1457 : W := mkw 0xb002040941464cf5 0xc3fffdffb010d956 0xfc000007c7fffffc 0x7ffffffff000ffff

def z1458 : W := mkw 0x2000000040040081 0x0301a0e090008102 0xfc000007c70007ac 0x5b83e3e1f000e007

def z1459 : W := mkw 0x0000000000000060 0x02d411bb20000000 0xfc000000000003cc 0x03fc03fff0000000

def z1460 : W := mkw 0xa0000000400400e5 0x024091ffb0008102 0xfc000000003fc40c 0x180003fff0000387

def z1461 : W := mkw 0x8000000000000094 0x039de8e690000000 0x0c00000000000184 0x038fe3e670000000

def z1462 : W := mkw 0x0000000000000074 0x0163351930000000 0xfc0000000000037c 0x00731f99f0000000

def z1463 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xffffffc7ff3fc7ef 0xdbf3e3e1ffe7e387

def z1464 : W := mkw 0xb002040941464cf5 0xc3fffdffb010d956 0xfc0f003fc7c1c7fd 0x7ffffffff018fd9f

def z1465 : W := mkw 0x2b4fb52576248091 0x33bfece09739e982 0xfc0fe0380701c3fd 0x03ffffe1f718e180

def z1466 : W := mkw 0xb002040941464cf5 0xc39df8f79010d956 0xfc0f1e3fc7ffffff 0xff8ffffff018ffff

def z1467 : W := mkw 0x82495090002120f4 0x03fffdffb5280088 0xfffffff80001c3ff 0x87fffffffff80198

def z1468 : W := mkw 0x80000000000000e4 0x0349f9ffb0000000 0xfc000000000003fc 0x038ffffff0000000

def z1469 : W := mkw 0x038e9d2724000014 0x23f725aa337b6c00 0x0fffffffffc00107 0xe3f303807ffffc00

def z1470 : W := mkw 0xf955200cd36ecfeb 0xd0009255ce05b3d7 0xf3ffe007ff3ffc0b 0x5c00007f8f07e3ff

def z1471 : W := mkw 0x54300240889a130a 0xc800020048841265 0x03f01fc0003e3c02 0x9800000008e00267

def z1472 : W := mkw 0x57be9f67ac9a137a 0xe9bf7e114bff7e65 0xf3fffffffffe3ffb 0xfbfffc198ffffe67

def z1473 : W := mkw 0x0000000000000014 0x03ff6daa30000000 0x0c00000000000134 0x03f3ff8070000000

def z1474 : W := mkw 0x8000000000000064 0x024011bf30000000 0x0c00000000000004 0x0000039e70000000

def z1475 : W := mkw 0x8000000000000094 0x03dde9ee90000000 0xfc000000000003ec 0x03ffe3fff0000000

def z1476 : W := mkw 0xb002040941464cf5 0xc3fffdffb010d956 0xfc0f0007c7ffc7ff 0x7bfffffff000ff87

def z1477 : W := mkw 0x1000000000020060 0xc040111920001044 0xfc001e07c0fe3e7e 0xf8001f99f0001e67

def z1478 : W := mkw 0x038e9d27240000f0 0x23fffdf9b37b6c00 0xffffffffffc003ff 0xe3fffff9fffffc00

def z1479 : W := mkw 0x0000000000000000 0x0040010820000000 0x0c00000000000004 0x0000038070000000

def z1480 : W := mkw 0x54b20e43889a130a 0xc800020048d65e65 0x03ff1ffffffe3c03 0xf800000008fffe67

def z1481 : W := mkw 0x0000000000000000 0x036325a830000000 0x0c00000000000104 0x03f3038070000000

def z1482 : W := mkw 0xb4a20e4b49d65cf5 0xcbfffdffb0d2dd76 0xfc0f1fffc7ffffff 0xfffffffff0f8ffff

def z1483 : W := mkw 0x9002040901424cf4 0xc3fffdffb0105854 0xfc001e3fc0fe3ffe 0xfffffffff0181e7f

def z1484 : W := mkw 0x2000000040040081 0x0000804080008102 0xfc0f0007c73fc7af 0x5803e3e1f000e387

def z1485 : W := mkw 0x2bcfbd2776248091 0x33bfece0977bed82 0xffffffffffc1c3ff 0xe3ffffe1fffffd80

def z1486 : W := mkw 0xf4300248c9de5feb 0xc8009255c8849377 0xf0000000003ffc08 0x1c00007f800003ff

def z1487 : W := mkw 0x1480084208821060 0xc862151920421444 0xfc00000000c0037c 0x20731f99f0001c00

def z1488 : W := mkw 0x7957240dd36ecf0b 0xd1096a004e15fbd7 0x03fffe3ffffffff3 0xff8ffc000f1fffff

def z1489 : W := mkw 0x0000000000000064 0x026215bb30000000 0xfc0000000000037c 0x00731f99f0000000

def z1490 : W := mkw 0x0000000000000080 0x0341a1e890000000 0xfc000000000003ec 0x03f3e3f9f0000000

def z1491 : W := mkw 0x54300240889a136a 0xc800121148841265 0xf0000000003e3c08 0x1800001980000267

def z1492 : W := mkw 0x038c992624000074 0x23f735bb336b2400 0xfff0ffc7f8c0037e 0xe3f31f99ffe71c00

def z1493 : W := mkw 0x80000000000000e4 0x024091ffb0000000 0xfc0000000000032c 0x000303fff0000000

def z1494 : W := mkw 0x94a20e4b09d25ce0 0xc86add5da0d25c74 0xfc001ff800c03bfc 0xa47ffffff0f81c78

def z1495 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc0000000000007c 0x007ffffff0000000

def z1496 : W := mkw 0x0000000000000014 0x03f725aa30000000 0x0c0000000000038c 0x03f303e070000000

def z1497 : W := mkw 0x030e952524000070 0x21ff7d1923396800 0xfc0fe038070003fd 0x03ffff99f718e000

def z1498 : W := mkw 0xf7be9f6fedde5feb 0xe808da55cbffff77 0xf3fffffffffffefb 0xfc0cfc7f8fffffff

def z1499 : W := mkw 0x830c1004000000f4 0x03fffdffb3292000 0xffffffffff0003ff 0xc3ffffffffffe000

def z1500 : W := mkw 0x0000000000000000 0x030120a010000000 0x0c000000000003a4 0x0383e38070000000

def z1501 : W := mkw 0x74b00a42c89e138b 0xc8008240c8c69767 0xf3ff1fc7fffffeab 0xf800e06188e7ffe7

def z1502 : W := mkw 0xf4b20e4bc9de5f6b 0xc86a5f1d68d6df77 0x03ff1ffffffffc53 0xfc7c1c1e08ffffff

def z1503 : W := mkw 0x6df52a46dabc930b 0x180002004ec7a7a3 0x03ffe1c7ff3fc403 0x580000000fe7e387

def z1504 : W := mkw 0x54b00a42889a1060 0xc862151960c61465 0xfc001fc7f8c03f7c 0xf8731f99f0e71c67

def z1505 : W := mkw 0x54b00a42889a136a 0xc800121148c61665 0x03f01fc7f8fe3c52 0xf8001c1808e71e67

def z1506 : W := mkw 0x80000000000000e4 0x02f695ffb0000000 0xfc000000000003fc 0x03ff1ffff0000000

def z1507 : W := mkw 0x54b00a42889a130a 0xc800020048c61665 0x03f001c7f8c00400 0x7800000008e71c07

def z1508 : W := mkw 0x6bdfbd27f62c838b 0x3008ca40cf7fef83 0xf3ffffffffffc6fb 0xf80cfc618fffff87

def z1509 : W := mkw 0x8000000000000074 0x00fe5d1f20000000 0x0c00000000000154 0x007f1f9e70000000

def z1510 : W := mkw 0x81060405000000f4 0x03fffdffb2116800 0xfffffe3fffc003ff 0xe3ffffffff1ffc00

def z1511 : W := mkw 0xb000000841464cf5 0xc3fffdffb0009156 0xfc000000000007fc 0x1bfffffff0000007

def z1512 : W := mkw 0x69142004d20c830b 0x100002004a05a303 0x03f00007ff3e0402 0x580000000807e207

def z1513 : W := mkw 0x9002040901424cf4 0xc3fffdffb0105854 0xfc0f1e3fc7c03bff 0xe7fffffff018fc78

def z1514 : W := mkw 0x2000000040040081 0x020080e090008102 0xfc0f0007c73fc6af 0x5800e3e1f000e387

def z1515 : W := mkw 0x54b00a42889a136a 0xc800121148c61665 0xf3f01fc7f8fe3c0a 0xf800001988e71e67

def z1516 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x03ffffffffc03bf3 0xe7fffc1e0ffffc78

def z1517 : W := mkw 0x68512000d22c838b 0x10008240cc048383 0xf00f0007c73fc6ab 0x5800e0618000e387

def z1518 : W := mkw 0x69552004d22c830b 0x130122a05e05a383 0x03ffe007ff3fc403 0x5b8000000f07e387

def z1519 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc0f1e38000003ff 0x83fffffff0180000

def z1520 : W := mkw 0x2904200452048081 0x1301a0e09201a102 0xfc000000070003ac 0x0383e3e1f000e000

def z1521 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xffffe03fff3fc7af 0x5f8fe3e7ff1fe39f

def z1522 : W := mkw 0x0000000000000080 0x02d481ea90000000 0xfc000000000003cc 0x03fc03fff0000000

def z1523 : W := mkw 0x9002040901424cf4 0xc3fffdffb0105854 0xfc00000000c003fc 0x23fffffff0001c00

def z1524 : W := mkw 0x54b00a42889a130a 0xc822060048c61665 0x03f01fc7f8fe3c52 0xf8701c0008e71e67

def z1525 : W := mkw 0xb000000841464ce5 0xc2d491ffb0009156 0xfc0f1e38003fffcf 0x9ffc03fff01803ff

def z1526 : W := mkw 0xf8716298d37fefeb 0xd24093ffdc8493ff 0xfc000000003ffc0c 0x1c0003fff00003ff

def z1527 : W := mkw 0xb002040941464cf5 0xc3fffdffb010d956 0xfc0f0038073ffffd 0x1ffffffff018e3ff

def z1528 : W := mkw 0xe955200cd36ccf8b 0x1301a2e4de05a393 0xffffe007ff3fc7af 0x5f83e3e7ff07e39f

def z1529 : W := mkw 0x80000000000000e0 0x0008d85580000000 0xfc000000000003fc 0x000ffffff0000000

def z1530 : W := mkw 0x82aadfb3241120f4 0x23fffdffb1fa4c28 0xfc001ff800c03bfc 0xa7fffffff0f81c78

def z1531 : W := mkw 0x69142004d20c838b 0x1101a240da05a303 0xffffe007ff3e07af 0x5b83e381ff07e207

def z1532 : W := mkw 0x8000000000000074 0x02fe5dbf20000000 0xfc000000000003fc 0x03ff1ffff0000000

def z1533 : W := mkw 0x0000000000000080 0x0395a0e290000000 0xfc000000000003ac 0x038fe3e7f0000000

def z1534 : W := mkw 0xb24b549941676cf5 0xc3fffdffb538d9de 0xfc0ffe3fc7ffffff 0xfffffffff718ffff

def z1535 : W := mkw 0x0249509000212014 0x03f725aa35280088 0x0c0fe0380001c185 0x07ff03e677180198

def z1536 : W := mkw 0x0000000000000060 0x0040111920000000 0xfc0000000000034c 0x00700399f0000000

def z1537 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x03f0ffc7ffc00372 0xe3f3fc000fe7fc00

def z1538 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xfff001c7f8c0077c 0x78731f99f8e71c07

def z1539 : W := mkw 0x0000000000000080 0x0301a0e090000000 0xfc0f0000003fc3af 0x0383e3e1f0000380

def z1540 : W := mkw 0xf996ad2ff74eccf1 0xf12bfc55d257fd57 0xfc000007ffc00434 0x7803fc01f007fc07

def z1541 : W := mkw 0x0104000400000080 0x0301a0e092012000 0xfff0e000380003ac 0x0383e3e1ff070000

def z1542 : W := mkw 0x838e9d2724000074 0x23ff7dbf337b6c00 0x0fffffffffc003f7 0xe3ffff9e7ffffc00

def z1543 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x03fffffffffffbf3 0xe7fffc000ffffff8

def z1544 : W := mkw 0xb000000841464cf5 0xc3fffdffb0009156 0xfc001e07c0fffffe 0xfffffffff0001fff

def z1545 : W := mkw 0x90000000000200f4 0xc3fffdffb0001044 0xfc000000003e3ffc 0x1bfffffff0000267

def z1546 : W := mkw 0x8000000000000074 0x02fe5dbf30000000 0x0c00000000000054 0x007c1f9e70000000

def z1547 : W := mkw 0x038c992624000070 0x21f73519236b2400 0xfff0e1c03800037c 0x03f31f99ffe70000

def z1548 : W := mkw 0x47bc9b66ac98131a 0x29b726004bef2621 0x03f0e1c038000100 0x03f300000fe70000

def z1549 : W := mkw 0x14a00a4208921060 0xc862151920c21464 0xfc001fc7c0fe3f7e 0xf8731f99f0e01e67

def z1550 : W := mkw 0xb1868d2f65464cf5 0xe3fffdffb253fd56 0xfc0f1e3fffffffff 0xfffffffff01fffff

def z1551 : W := mkw 0x80204290001120e4 0x024091ffb0800028 0xfc0000000000380c 0x040003fff0000078

def z1552 : W := mkw 0xb002040941464cf5 0xc2feddffb010d956 0xfc001e3800fffc5c 0xbc7c1ffff0181fff

def z1553 : W := mkw 0xa002040941444cf5 0x03fffdffb010c912 0xfc0f1e3fc7c1c3ff 0xe7fffffff018fd98

def z1554 : W := mkw 0x0000000000000060 0x0000101100000000 0xfc0000000000037c 0x00031f99f0000000

def z1555 : W := mkw 0xa002040941444c95 0x03ffedeeb010c912 0x0c0f00380701c185 0x07ffe3e67018e198

def z1556 : W := mkw 0x138e9d2724020070 0xe1ff7d19237b7c44 0xfffffffffffe3fff 0xfbffff99fffffe67

def z1557 : W := mkw 0x40b00a028018030a 0x0062070848c60621 0xfff01fc7f8fe3f7e 0xf8731f99f8e71e67

def z1558 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xffffe007ff3fc527 0x5b83e381ff07e387

def z1559 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc0000000000015c 0x03ff1ffff0000000

def z1560 : W := mkw 0x0002040100000014 0x03ff6daa30104800 0x0c0f1e3fc7c003f7 0xe3ffff807018fc00

def z1561 : W := mkw 0x69752204d23c830b 0x100002004e85a3a3 0x03ffffc7ff3ffc03 0xd80000000fe7e3e7

def z1562 : W := mkw 0x90000000000200f4 0xc3fffdffb0001044 0xfc000007c0c007fc 0x7bfffffff0001c07

def z1563 : W := mkw 0x838e9d27240000f4 0x23fffdffb37b6c00 0xfff0e1c7ffc003fc 0x63ffffffffe7fc00

def z1564 : W := mkw 0x401000008008030a 0x0000020048040201 0x03f00007f83e0722 0x5803000008070207

def z1565 : W := mkw 0x54b00a42889a130a 0xc800020048c61665 0x03f001c0383e3c00 0x1800000008e70267

def z1566 : W := mkw 0x80000000000000e4 0x026295ffb0000000 0xfc0000000000010c 0x007303fff0000000

def z1567 : W := mkw 0x96aa9f632c921074 0xe8fe5d1f21fa5c64 0x00001ff800c03850 0xa07c1c1e00f81c60

def z1568 : W := mkw 0x0000000000000014 0x03ff6daa30000000 0x0c00000000000184 0x03ffe38070000000

def z1569 : W := mkw 0x80000000000000e0 0x0208d8f590000000 0xfc000000000002fc 0x000cfffff0000000

def z1570 : W := mkw 0xb0000000400600f5 0xc3fffdffb0009146 0xfc0f1e07c7ffffff 0xfbfffffff000ffe7

def z1571 : W := mkw 0x401000008008030a 0x0000020048040201 0x00000000003e0400 0x1800000000000207

def z1572 : W := mkw 0x0000000000000010 0x01bf6c0000000000 0xfc000000000003fc 0x03ffff81f0000000

def z1573 : W := mkw 0x0000000000000080 0x0323a4e090000000 0xfc000000000003fc 0x03f3ffe1f0000000

def z1574 : W := mkw 0x69d52806d22c830b 0x100002004e47a783 0x03ffffc7ffffc403 0xf80000000fe7ff87

def z1575 : W := mkw 0x69552004d22c831b 0x11bf6e004e05a383 0x03ffe007ff3fc7f3 0x5bfffc000f07e387

def z1576 : W := mkw 0x10000000000200e0 0xc301b0f190001044 0xfc001e07c0fe3ffe 0xfb83fff9f0001e67

def z1577 : W := mkw 0x038e9d2724000074 0x23ff7dbb337b6c00 0xffffffffffc003ff 0xe3ffff99fffffc00

def z1578 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0x03fffff80001f9c1 0x87fc03fe0ff801f8

def z1579 : W := mkw 0x0000000000000000 0x03d521aa10000000 0x0c00000000000104 0x03f3038070000000

def z1580 : W := mkw 0x0000000000000094 0x03f7a5eab0000000 0xfc000000000003ec 0x03ffe3fff0000000

def z1581 : W := mkw 0x439e9d27a408030a 0x200002004b7f6e01 0x03fffffffffe0403 0xf80000000ffffe07

def z1582 : W := mkw 0x006102000030030a 0x024003a80c8002a0 0x03fffff8003ffbcb 0x87fc03fe0ff803f8

def z1583 : W := mkw 0x80000000000000f4 0x0363b5ffb0000000 0xfc0000000000000c 0x000303fff0000000

def z1584 : W := mkw 0xa0000000400400f5 0x03fffdffb0008102 0xfc000000003fc7fc 0x1bfffffff0000387

def z1585 : W := mkw 0x8000000000000094 0x03ffedeeb0000000 0xfc000000000003ac 0x03ffe3e7f0000000

def z1586 : W := mkw 0x3002040941464c61 0xc06215192010d956 0xfc0f1e3fc7ffff7f 0xfc731f99f018ffff

def z1587 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xffffffc7f8fe3fff 0xfbf31f99ffe71e67

def z1588 : W := mkw 0x409008028008030a 0x0000020048460601 0x03f01fc7f8fe0402 0xf800000008e71e07

def z1589 : W := mkw 0x0000000000000060 0x0040111920000000 0xfc0000000000027c 0x00001f99f0000000

def z1590 : W := mkw 0x0000000000000080 0x020080e090000000 0xfc000000000002ac 0x0000e3e1f0000000

def z1591 : W := mkw 0x0000000000000060 0x036335b930000000 0xfc0000000000037c 0x03f31f99f0000000

def z1592 : W := mkw 0x6b5d7094d22da30b 0x129402a24f2da38b 0x03ffe03fff3fc483 0x5f8c00660f1fe39f

def z1593 : W := mkw 0x9002040901424cf4 0xc3fffdffb0105854 0xfc0f1e3800fffbff 0xa7fffffff0181ff8

def z1594 : W := mkw 0xb002040941464ce1 0xc008d8558010d956 0xf00f1e3807fffcd9 0xbc0cfc7f8018ffff

def z1595 : W := mkw 0x90800802000200f4 0xc3fffdffb0421444 0xfff01fc7f8fe3ffe 0xfbfffffff8e71e67

def z1596 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xfff01ffff8fe3f7e 0xfc7f1f9ff8ff1e7f

def z1597 : W := mkw 0x0228529000112014 0x03f725aa31a80028 0x0c001ff800003944 0x87ff039e70f80078

def z1598 : W := mkw 0x0000000000000060 0x006a5d1920000000 0xfc000000000003fc 0x007fff99f0000000

def z1599 : W := mkw 0x80000000000000f4 0x03f7b5ffb0000000 0xfc00000000000104 0x03f30381f0000000

def z1600 : W := mkw 0x80000000000000e4 0x02d491ffb0000000 0xfc0000000000010c 0x03f003fff0000000

def z1601 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0x03fffffff83ffbeb 0xc7ff03fe0fff03f8

def z1602 : W := mkw 0x026952900031230a 0x02d403aa0da802a8 0x03ffffffc0fffbfb 0xe7fc1ffe0ff81ff8

def z1603 : W := mkw 0x0000000000000094 0x03f7a5eab0000000 0x0c00000000000184 0x03f3e3e070000000

def z1604 : W := mkw 0x0000000000000080 0x0301a0e090000000 0xfff00007f80003ae 0x4383e3e1f8070000

def z1605 : W := mkw 0x80000000000000f4 0x03ddf9ffb0000000 0xfc000000000002fc 0x038cfffff0000000

def z1606 : W := mkw 0x8000000000000074 0x03ff7dbf30000000 0x0c000000000003f4 0x03ffff9e70000000

def z1607 : W := mkw 0x70120409c14e4f0b 0xc00002004814db57 0x03ff1e3ffffffc03 0xfc000000081fffff

def z1608 : W := mkw 0x80000000000000e4 0x0341b1ffb0000000 0xfc0000000000008c 0x0380e3fff0000000

def z1609 : W := mkw 0x80820c03000000f4 0x03fffdffb0524c00 0xffff1fffffc003ff 0xe3fffffff8fffc00

def z1610 : W := mkw 0x83aedfb7241120f4 0x23fffdffb3fb6c28 0xffffffffffc03bff 0xe7fffffffffffc78

def z1611 : W := mkw 0x0000000000000004 0x024001aa30000000 0x0c0000000000000c 0x000003fe70000000

def z1612 : W := mkw 0x495520049228830a 0x100002004e052281 0x03ffe000383fc003 0x000000000f070380

def z1613 : W := mkw 0x7bdfbd2ff76ecf0b 0xf00002004f7fffd7 0x03fffffffffffc03 0xfc0000000fffffff

def z1614 : W := mkw 0x828a9d23240000f4 0x23fffdffb17a4c00 0xfff01ffff8c003fe 0xe3fffffff8ff1c00

def z1615 : W := mkw 0x4bdfbd27b628831a 0x31bf6e004f7f6e81 0x03ffffffffc003f3 0xe3fffc000ffffc00

def z1616 : W := mkw 0x56f95ad288bb330a 0xca9402a24dee16ed 0x03fffffff8fffc83 0xff8c00660fff1fff

def z1617 : W := mkw 0x81868d27240000f4 0x23fffdffb2536c00 0xfff01fc7ffc003fe 0xe3fffffff8e7fc00

def z1618 : W := mkw 0x0000000000000080 0x0101a04090000000 0xfc0000000000032c 0x0003e381f0000000

def z1619 : W := mkw 0x495520049228830a 0x130122a05e052281 0xffffe007ff3e07af 0x5b83e381ff07e207

def z1620 : W := mkw 0x0000000000000080 0x020080e090000000 0xfc0000000000032c 0x000303e1f0000000

def z1621 : W := mkw 0x0000000000000080 0x0301a0e090000000 0xfc0f0007c70003af 0x4383e3e1f000e000

def z1622 : W := mkw 0x80020401000000e4 0x0248d9ffb0104800 0xfc0f1e3fc7c002ff 0xe00cfffff018fc00

def z1623 : W := mkw 0x0000000000000070 0x01f7351920000000 0xfc0000000000037c 0x03f31f99f0000000

def z1624 : W := mkw 0x30000000400600e1 0xc000905180009146 0xf00f1e3fc7fffefb 0xfc0cfc7f8018ffff

def z1625 : W := mkw 0xa002040941444ce1 0x006add5da010c912 0xfc0f00380701c3fd 0x047ffffff018e198

def z1626 : W := mkw 0x44b00a428898130a 0x0822060048c60621 0x03f01fc7f8c00372 0xe0731c0008e71c00

def z1627 : W := mkw 0x90000000000200f4 0xc3fffdffb0001044 0xfc0f1e3fc0ffffff 0xfffffffff0181fff

def z1628 : W := mkw 0x80000000000000e4 0x026295ffb0000000 0xfc0000000000005c 0x00701ffff0000000

def z1629 : W := mkw 0x0228529000112080 0x03d5a1ea91a80028 0xfc001ff800003bec 0x87ffe3fff0f80078

def z1630 : W := mkw 0x6b7d7294d23da30b 0x100002004fada3ab 0x03ffe1c7ff3fc403 0x580000000fe7e387

def z1631 : W := mkw 0x57be9f67ac9a136a 0xe8085a114bff7e65 0xf3fffffffffe3efb 0xf80cfc198ffffe67

def z1632 : W := mkw 0xb002040941464cf5 0xc36bfdffb010d956 0xfc000007c7fffc3c 0x7c03fffff000ffff

def z1633 : W := mkw 0x80000000000000f4 0x032bfcf5b0000000 0xfc0000000000003c 0x0003ffe1f0000000

def z1634 : W := mkw 0x038c992624000090 0x23b7a4e0936b2400 0xfff0e1c0380003ac 0x03f3e3e1ffe70000

def z1635 : W := mkw 0x0000000000000000 0x03d521aa10000000 0x0c000000000003cc 0x03ff03fe70000000

def z1636 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0x03f01fc038c03850 0xa0701c1808e71c60

def z1637 : W := mkw 0x80000000000000e0 0x0040915da0000000 0xfc0000000000000c 0x000003fff0000000

def z1638 : W := mkw 0x2945200452248081 0x1301a0e09601a182 0x0c0fe0000701c185 0x0383e3e07700e180

def z1639 : W := mkw 0x0000000000000060 0x026215bb20000000 0xfc0000000000037c 0x00731ffff0000000

def z1640 : W := mkw 0x76fb5edbc9ff7f0b 0xc80002004dfedfff 0x03fffffffffffc03 0xfc0000000fffffff

def z1641 : W := mkw 0x0000000000000000 0x0000000000000000 0xfc0000000000000c 0x00000381f0000000

def z1642 : W := mkw 0x2000000040040081 0x0301a0e090008102 0xfc000000003fc7ac 0x1b83e3e1f0000387

def z1643 : W := mkw 0x80000000000000e4 0x0062955db0000000 0xfc0000000000037c 0x00731f99f0000000

def z1644 : W := mkw 0xb002040941464ce5 0xc2dcd9ffb010d956 0xfc0f1e3fc7ffffff 0xfffcfffff018ffff

def z1645 : W := mkw 0x6b7d7294d23da30b 0x119522004fada3ab 0x03ffffffff3fffe3 0xdfffe0000fffe3ff

def z1646 : W := mkw 0xab4d70945225a0f5 0x13fffdffb729a18a 0xfc0fe0380701c3fd 0x07fffffff718e198

def z1647 : W := mkw 0x0000000000000060 0x02f615bb20000000 0xfc0000000000037c 0x03f31f99f0000000

def z1648 : W := mkw 0xa002040941444cf5 0x03fffdffb010c912 0xfc0f003fc73fc7ff 0x5ffffffff018e39f

def z1649 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc0000000000013c 0x03f3fffff0000000

def z1650 : W := mkw 0x8000000000000094 0x03f7a5eeb0000000 0x0c00000000000104 0x03f303e670000000

def z1651 : W := mkw 0x60100000c00c038b 0x00008240c8048303 0xf3ff0007ff3fc6ab 0x5800e0618807e387

def z1652 : W := mkw 0x69552004d22c830b 0x100002004e05a383 0x03ffe007ff3fc783 0x5b8000000f07e387

def z1653 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xfff0e007ff0007ac 0x5b83e3e1ff07e007

def z1654 : W := mkw 0x00000000000000f0 0x03fffdf9b0000000 0xfc000000000003fc 0x03fffff9f0000000

def z1655 : W := mkw 0x0104000400000014 0x03f725aa32012000 0x0fffe007ff0003a7 0x43f3e3807f07e000

def z1656 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xffff1fc7f8ffffff 0xf8731ff9f8e71fe7

def z1657 : W := mkw 0x038e9d2724000010 0x21bf6c00037b6c00 0x03f0e1c7ffc003f0 0x63fffc000fe7fc00

def z1658 : W := mkw 0x0000000000000014 0x03ff6daa30000000 0x0c00000000000154 0x03ff1f8070000000

def z1659 : W := mkw 0x830e952524000094 0x239de8e693396800 0xffffe03fff0003af 0x438fe3e7ff1fe000

def z1660 : W := mkw 0xa1040004400400f5 0x03fffdffb201a102 0xffffe007ff3fc7ff 0x5bffffffff07e387

def z1661 : W := mkw 0x01860c0700000000 0x012b6c0002536c00 0x03ffffffffc003f3 0xe3fffc000ffffc00

def z1662 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xfffffe3fff3fc7ef 0xdb8fe3e1ff1fe387

def z1663 : W := mkw 0x2002040140040081 0x0008c8408010c902 0xf00f1e3fc7fffefb 0xfc0cfc7f8018ffff

def z1664 : W := mkw 0x80000000000000e4 0x024091ffb0000000 0xfc0000000000038c 0x038003fff0000000

def z1665 : W := mkw 0x80000000000000e0 0x036bfdfdb0000000 0xfc000000000003fc 0x03fffffff0000000

def z1666 : W := mkw 0x54b00a42889a136a 0xc862171968c61665 0xfc001fc7f8fe3c7c 0xf8731f99f0e71e67

def z1667 : W := mkw 0x54b00a42889a130a 0xc800020048c61665 0x03f01fc7f8fe3f42 0xf870000008e71e67

def z1668 : W := mkw 0x8000000000000074 0x006a5d1d20000000 0xfc0000000000037c 0x00731f99f0000000

def z1669 : W := mkw 0x0104000400000014 0x03f725aa32012000 0x0ff0e00038000104 0x03f303807f070000

def z1670 : W := mkw 0x6bdfbd27f62c839b 0x33bfeee0df7fef83 0x03ffffffffffc7f3 0xfbfffc600fffff87

def z1671 : W := mkw 0x415500048028030a 0x030122a04e052281 0xffffe007ff3fc7af 0x5b83e3e1ff07e387

def z1672 : W := mkw 0x80204290001120f4 0x03fffdffb0800028 0xfc00000000003bfc 0x07fffffff0000078

def z1673 : W := mkw 0x78512008d36ecf0b 0xd00002004c0493d7 0x00000000003ffc00 0x1c000000000003ff

def z1674 : W := mkw 0x80000000000000e4 0x0248d9ffb0000000 0xfc0000000000005c 0x000c1ffff0000000

def z1675 : W := mkw 0x1000000000020060 0xc062151920001044 0xfc001e0000c03b7c 0xa0731f99f0001c60

def z1676 : W := mkw 0x54300240889a130a 0xc800020048841265 0x03f00007f83e3c02 0x5800000008070267

def z1677 : W := mkw 0x57bc9b66ac9a130a 0xe80002004bef3665 0x03f0ffc7f8fe3c02 0xf80000000fe71e67

def z1678 : W := mkw 0x7df72e4fdbfedf0b 0xd80002004ed7fff7 0x03fffffffffffc03 0xfc0000000fffffff

def z1679 : W := mkw 0x1000000000020074 0xc3f735bb30001044 0xfc001e07c0fe3f7e 0xfbf31f99f0001e67

def z1680 : W := mkw 0x3002040941464c81 0xc301a0e09010d956 0xfc0f1e3fc7ffffaf 0xff83e3e1f018ffff

def z1681 : W := mkw 0x0000000000000080 0x020080e090000000 0xfc0000000000038c 0x038003e1f0000000

def z1682 : W := mkw 0x838e9d27240000f4 0x23fffdffb37b6c00 0xfc0fe03fffc003fd 0x63fffffff71ffc00

def z1683 : W := mkw 0x47fddbf6acb9331a 0x2bf727aa6fef26a9 0x0ff0e1c038000104 0x03f303807fe70000

def z1684 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xffffe007ff3fffaf 0x5f83e3ffff07e3ff

def z1685 : W := mkw 0x030c912424000014 0x23f725aa33292000 0x0c00e00000000104 0x03f3038077000000

def z1686 : W := mkw 0x495520049228830a 0x100002004e052281 0x03ffe007ff000003 0x400000000f07e000

def z1687 : W := mkw 0x14a00a42089210e0 0xcb63b5f9b0c21464 0xfc001fc000c03bfc 0xa3f3fff9f0e01c60

def z1688 : W := mkw 0xb20a140941464cf5 0xc3fffdffb138d956 0xffffffffc7ffffff 0xfffffffffff8ffff

def z1689 : W := mkw 0x68512000d22c830b 0x100002004c048383 0x03ffe000003fc403 0x180000000f000387

def z1690 : W := mkw 0x80000000000000e4 0x02d491ffb0000000 0xfc0000000000008c 0x038c03fff0000000

def z1691 : W := mkw 0x69552004d22c830b 0x100002004e05a383 0x03fffe3fff3ffecb 0xdc0c007e0f1fe3ff

def z1692 : W := mkw 0xb38e9d2f65464cf1 0xe3bffcf5937bfd56 0xffffffffffffffff 0xffffffffffffffff

def z1693 : W := mkw 0x69552004d22c830b 0x110122004e05a383 0x03ffe007ff3fc503 0x5b8300000f07e387

def z1694 : W := mkw 0x0000000000000014 0x03f725aa30000000 0xfc0000000000032c 0x03f30381f0000000

def z1695 : W := mkw 0x401000008008030a 0x0000020048040201 0xf3f00007f83e062a 0x5800000188070207

def z1696 : W := mkw 0xf0120409c14e4feb 0xc008da55c814db57 0xf3ff1e3ffffffefb 0xfc0cfc7f881fffff

def z1697 : W := mkw 0x80000000000000e4 0x026295ffb0000000 0xfc0000000000003c 0x00031ffff0000000

def z1698 : W := mkw 0x0000000000000060 0x00f6151b20000000 0xfc0000000000037c 0x007f1f9ff0000000

def z1699 : W := mkw 0x0000000000000000 0x0000000000000000 0xfc000007c03e072e 0x58030381f0000207

def z1700 : W := mkw 0x838e9d27240000f0 0x21fffd5da37b6c00 0xffffffffffc003ff 0xe3fffffffffffc00

def z1701 : W := mkw 0x68512000d22c838b 0x10008240cc048383 0xf0000000003fc408 0x1800006180000387

def z1702 : W := mkw 0x0000000000000060 0x0062151920000000 0xfc0000000000010c 0x00730399f0000000

def z1703 : W := mkw 0x00000000000000f4 0x03f7b5fbb0000000 0xfc000000000003fc 0x03f3fff9f0000000

def z1704 : W := mkw 0x54b00a42889a130a 0xc800020048c61665 0x03f01fc038c03800 0xa000000008e71c60

def z1705 : W := mkw 0x7fffbf67febe930b 0xf80002004fffffe7 0x03fffffffffffc03 0xf80000000fffffe7

def z1706 : W := mkw 0x79552004d22e836b 0xd00012114e05b3c7 0xf3fffe07fffffe7b 0xf8001c198f07ffe7

def z1707 : W := mkw 0x0000000000000080 0x0341a1ea90000000 0xfc000000000003ac 0x0383e3fff0000000

def z1708 : W := mkw 0xfbdfbd2ff76ecffb 0xf1bffe55cf7fffd7 0xf3fffffffffffffb 0xfffffc7f8fffffff

def z1709 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfc0000000000037c 0x03f3ff99f0000000

def z1710 : W := mkw 0x80000000000000f4 0x016bfd5db0000000 0xfc000000000003fc 0x007ffffff0000000

def z1711 : W := mkw 0x82889922240000f4 0x23fffdffb16a0400 0xfc0001c0000003fc 0x03fffffff0e00000

def z1712 : W := mkw 0x0000000000000000 0x0062050820000000 0x0c00000000000374 0x00731f8070000000

def z1713 : W := mkw 0xf4b20e4bc9de5feb 0xc86adf5de8d6df77 0xf3ff1ffffffffefb 0xfc7cfc7f88ffffff

def z1714 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xfc0fe007ff3fc4ad 0x5b83e3e1f707e387

def z1715 : W := mkw 0x77be9f6fedde5f0b 0xe80002004bffff77 0x03fffffffffffc03 0xfc0000000fffffff

def z1716 : W := mkw 0xf8532409d36ecfeb 0xd008da55cc14dbd7 0xf00f1e3fc7fffefb 0xfc0cfc7f8018ffff

def z1717 : W := mkw 0xb002040941464ce1 0xc36bfdfdb010d956 0xfc0f1e3fc7ffffff 0xfffffffff018ffff

def z1718 : W := mkw 0x0080080200000014 0x03f725aa30420400 0x0ff01fc7f8c00376 0xe3f31f8078e71c00

def z1719 : W := mkw 0x0000000000000014 0x02f605aa30000000 0x0c00000000000004 0x0070038070000000

def z1720 : W := mkw 0x80000000000000e0 0x0062955da0000000 0xfc0000000000037c 0x00731ffff0000000

def z1721 : W := mkw 0x0249509000212014 0x03f725aa35280088 0x0c00e00000000104 0x03f3038077000000

def z1722 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xfff0e007ff3e072e 0x5b83e381ff07e207

def z1723 : W := mkw 0xf957240dd36ecfeb 0xd309faf5de15fbd7 0xf3fffe3ffffffefb 0xff8cfc7f8f1fffff

def z1724 : W := mkw 0x80000000000000f4 0x03ddf9ffb0000000 0xfc000000000003cc 0x03fce3fff0000000

def z1725 : W := mkw 0x6b5d7094d22da30b 0x100002004f2da38b 0x03ffe03fff3fc403 0x5c0000000f1fe39f

def z1726 : W := mkw 0x030e952524000014 0x23ff6daa33396800 0x0c0fe03807000185 0x03ffe3807718e000

def z1727 : W := mkw 0x0269529000312000 0x02d401aa05a800a8 0x000ffff8003ffacb 0x87fc007e07f803f8

def z1728 : W := mkw 0x16aadff32c933070 0xe8fe5d1b21fa5c6c 0x00001ff800c03850 0xa47c1c1e00f81c78

def z1729 : W := mkw 0x56f95ad288bb330a 0xc80002004dee16ed 0x03f0ffc7f8fe3c02 0xf80000000fe71e67

def z1730 : W := mkw 0xb0820c0b41464ce1 0xc06add5da052dd56 0xffff1fffffffffff 0xfc7ffffff8ffffff

def z1731 : W := mkw 0xd4b20e4b89da5f6a 0xc8085a1548d65e75 0x03f01ffff8fe3c52 0xfc0c1c1e08ff1e7f

def z1732 : W := mkw 0x7bdfbd2ff76ecf1b 0xf1bf6e004f7fffd7 0x03fffffffffffff3 0xfffffc000fffffff

def z1733 : W := mkw 0x80000000000000f4 0x036bfdffb0000000 0xfc0000000000037c 0x0073fffff0000000

def z1734 : W := mkw 0x838e9d27240000f4 0x23fffdffb37b6c00 0xfc0ffff807c003fd 0xa3fffffff7f8fc00

def z1735 : W := mkw 0x0000000000000060 0x026215b920000000 0xfc000000000003fc 0x03f31ff9f0000000

def z1736 : W := mkw 0x022812000010030a 0x00d4030809a80220 0x03fffff8003ffbcb 0x87fc03fe0ff803f8

def z1737 : W := mkw 0x0000000000000060 0x0163351920000000 0xfc000000000003fc 0x03f3ff99f0000000

def z1738 : W := mkw 0x838c9926240000f4 0x23f7b5ffb36b2400 0xfff0e1c03800010c 0x03f303ffffe70000

def z1739 : W := mkw 0x4df52a469ab8930a 0x180002004ec726a1 0x03f0e1c038000000 0x000000000fe70000

def z1740 : W := mkw 0x7db42a46da9e930b 0xd80002004ac7b767 0x03f01fc7fffe3c02 0xf800000008e7fe67

def z1741 : W := mkw 0x69552004d22c838b 0x1301a2e0de05a383 0xffffe007ff01c5a5 0x5b83e3e1ff07e187

def z1742 : W := mkw 0x0000000000000014 0x03f725aa30000000 0x0c0000000000034c 0x03f3039870000000

def z1743 : W := mkw 0x81868d27240000f4 0x216bfd5db2536c00 0xfff01fc7ffc0037e 0xe073ff99f8e7fc00

def z1744 : W := mkw 0x80000000000000f4 0x03fffdffb0000000 0xfff00007f80003fe 0x43fffffff8070000

def z1745 : W := mkw 0x7955200cd36ecf0b 0xd00002004e05b3d7 0x03ffe007ff3ffc03 0x5c0000000f07e3ff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z1,z2,z9,z3,z6]),(0,[z0,z1,z10,z11,z2,z3,z6]),(1,[z0,z1,z2,z3,z12,z6])],[(0,[z0,z1,z2,z3,z13,z14,z6]),(0,[z0,z15,z1,z2,z3,z16,z6]),(0,[z17,z0,z1,z2,z3,z18,z6]),(0,[z0,z1,z19,z2,z3,z4,z6])],[(0,[z20,z21,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z22,z6]),(0,[z23,z0,z1,z2,z3,z24,z6]),(0,[z25,z0,z1,z2,z26,z4,z6]),(1,[z27,z0,z1,z2,z3,z6]),(0,[z28,z29,z0,z1,z2,z3,z6]),(0,[z0,z1,z30,z2,z3,z14,z6]),(0,[z0,z1,z31,z2,z3,z4,z6]),(0,[z32,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z33,z34])],[(0,[z0,z1,z2,z3,z35,z4,z6]),(0,[z0,z36,z1,z11,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z37,z6]),(1,[z0,z1,z2,z3,z38,z6]),(0,[z0,z1,z39,z11,z2,z3,z6])],[(0,[z0,z40,z41,z2,z3,z4,z6]),(0,[z0,z1,z2,z42,z3,z14,z6]),(0,[z0,z1,z2,z43,z3,z14,z6]),(0,[z29,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z44,z3,z45,z6]),(1,[z0,z1,z46,z2,z3,z6]),(0,[z17,z0,z1,z2,z3,z6,z33]),(0,[z0,z1,z47,z2,z3,z4,z6])],[(0,[z0,z1,z2,z42,z3,z6,z33]),(0,[z0,z1,z48,z2,z49,z4,z6]),(0,[z0,z1,z2,z3,z4,z50,z6]),(0,[z0,z1,z51,z2,z3,z6,z33]),(0,[z29,z0,z1,z2,z3,z6,z33]),(0,[z52,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z53,z3,z4,z6]),(0,[z0,z1,z54,z2,z55,z4,z6]),(0,[z0,z1,z56,z2,z3,z4,z6]),(0,[z57,z8,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z58,z6]),(0,[z0,z1,z59,z2,z3,z4,z6]),(0,[z60,z17,z0,z1,z2,z3,z6])],[(0,[z0,z1,z41,z11,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z61]),(0,[z0,z1,z2,z3,z4,z62,z6]),(0,[z0,z1,z63,z2,z3,z14,z6])]],
   [[(0,[z20,z1,z2,z3,z49,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z64]),(0,[z65,z0,z1,z2,z55,z3,z6]),(0,[z0,z1,z2,z3,z66,z4,z6]),(0,[z0,z1,z2,z3,z14,z67,z6]),(0,[z0,z1,z2,z3,z14,z6,z68]),(0,[z0,z1,z2,z3,z14,z69,z6]),(0,[z0,z1,z70,z2,z3,z4,z6]),(0,[z71,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z63,z2,z3,z6,z33])],[(0,[z72,z0,z1,z2,z3,z73,z6]),(1,[z0,z1,z54,z2,z4,z6]),(1,[z0,z1,z74,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z75,z6]),(0,[z76,z29,z0,z1,z2,z3,z6]),(0,[z17,z0,z1,z2,z44,z3,z6]),(0,[z0,z1,z2,z3,z77,z4,z6]),(0,[z0,z1,z2,z3,z78,z4,z6]),(0,[z0,z1,z79,z2,z3,z4,z6])],[(0,[z80,z1,z2,z3,z4,z81,z6]),(0,[z0,z1,z2,z42,z44,z3,z6]),(0,[z82,z0,z1,z2,z3,z6,z33]),(0,[z0,z1,z51,z2,z44,z3,z6]),(0,[z83,z0,z1,z2,z3,z4,z6]),(0,[z84,z0,z1,z2,z3,z4,z6]),(0,[z0,z40,z1,z2,z3,z14,z6]),(0,[z29,z0,z1,z2,z44,z3,z6]),(0,[z85,z0,z1,z2,z44,z3,z6])],[(0,[z86,z72,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z87,z16,z6]),(0,[z88,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z89,z2,z3,z4,z6]),(0,[z0,z1,z90,z2,z3,z4,z6])],[(0,[z17,z0,z1,z2,z42,z3,z6]),(0,[z8,z0,z1,z2,z3,z18,z6]),(0,[z0,z1,z2,z3,z4,z91,z6])],[(0,[z0,z1,z2,z3,z49,z4,z6]),(0,[z0,z1,z2,z3,z92,z16,z6]),(0,[z0,z1,z2,z3,z18,z16,z6]),(0,[z0,z1,z2,z3,z4,z6,z93]),(0,[z0,z1,z63,z2,z44,z3,z6])],[(0,[z94,z0,z1,z2,z3,z24,z6]),(0,[z25,z17,z0,z1,z2,z3,z6]),(0,[z0,z1,z95,z2,z3,z14,z6]),(0,[z17,z0,z1,z2,z3,z96,z6]),(0,[z0,z1,z2,z3,z4,z6,z97])],[(0,[z0,z1,z2,z98,z3,z4,z6]),(0,[z99,z0,z1,z2,z3,z4,z6]),(0,[z82,z0,z1,z2,z44,z3,z6]),(0,[z0,z1,z100,z2,z3,z4,z6]),(0,[z0,z1,z101,z2,z3,z4,z6]),(0,[z8,z0,z1,z2,z3,z6,z33]),(0,[z0,z102,z1,z2,z3,z4,z6])]],
   [[(0,[z80,z0,z41,z2,z3,z4,z6]),(0,[z0,z1,z2,z49,z4,z6,z103]),(0,[z23,z17,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z104,z4,z6]),(0,[z0,z1,z105,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z13,z16,z6]),(0,[z0,z1,z2,z3,z4,z6,z106]),(0,[z0,z1,z3,z18,z4,z6,z107]),(0,[z0,z1,z2,z3,z4,z108,z6]),(0,[z0,z1,z109,z2,z3,z6,z33])],[(1,[z0,z1,z2,z3,z66,z6]),(0,[z0,z1,z30,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z4,z110,z6]),(0,[z0,z1,z111,z2,z3,z4,z103])],[(0,[z112,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z113,z2,z3,z4,z6]),(0,[z25,z0,z114,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z115]),(0,[z0,z15,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z116,z14,z6])],[(0,[z0,z1,z2,z42,z3,z16,z6]),(0,[z117,z0,z1,z51,z2,z3,z6]),(0,[z29,z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z2,z44,z3,z18,z6]),(0,[z29,z0,z118,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z119,z4,z6]),(0,[z17,z0,z1,z2,z3,z78,z6])],[(0,[z0,z1,z2,z3,z4,z120,z6]),(0,[z0,z1,z2,z3,z4,z6,z121]),(0,[z0,z1,z2,z3,z122,z4,z6]),(0,[z123,z0,z1,z2,z3,z4,z6]),(0,[z25,z124,z1,z2,z3,z4,z6]),(0,[z82,z0,z1,z2,z3,z125,z6]),(0,[z0,z126,z1,z2,z3,z6,z33]),(0,[z0,z1,z2,z3,z6,z33,z68]),(1,[z0,z1,z2,z3,z127,z6]),(0,[z128,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z1,z2,z44,z3,z6]),(1,[z0,z1,z2,z3,z129,z6])],[(0,[z20,z0,z1,z2,z3,z6,z33]),(0,[z0,z1,z2,z3,z14,z24,z6]),(0,[z17,z0,z1,z2,z3,z87,z6]),(0,[z0,z1,z130,z2,z3,z4,z6]),(0,[z29,z0,z1,z2,z3,z131,z6]),(0,[z0,z1,z132,z2,z3,z4,z6])],[(0,[z80,z0,z1,z2,z3,z14,z6]),(0,[z133,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z26,z4,z6]),(0,[z25,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z63,z2,z3,z16,z6]),(0,[z134,z8,z0,z1,z2,z3,z6]),(0,[z0,z1,z135,z2,z3,z4,z136]),(0,[z0,z1,z2,z44,z3,z6,z33])],[(0,[z137,z0,z1,z2,z3,z4,z6]),(0,[z138,z0,z1,z2,z3,z4,z6]),(0,[z80,z0,z1,z2,z3,z6,z33]),(0,[z139,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z140]),(0,[z133,z0,z1,z2,z3,z6,z33]),(0,[z8,z0,z1,z2,z42,z3,z6]),(0,[z141,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z16,z6,z142]),(0,[z0,z1,z143,z2,z3,z4,z6])]],
   [[(0,[z23,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z144,z3,z4,z6]),(0,[z0,z145,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z81,z6,z146]),(0,[z0,z1,z147,z51,z2,z3,z6]),(0,[z148,z0,z1,z2,z3,z4,z6]),(0,[z149,z0,z1,z2,z3,z6,z68]),(0,[z0,z1,z150,z2,z3,z4,z6])],[(0,[z151,z0,z1,z2,z42,z3,z6]),(0,[z0,z40,z1,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z152,z4,z6]),(0,[z0,z126,z1,z2,z44,z3,z6]),(0,[z8,z0,z1,z2,z3,z96,z6])],[(0,[z20,z0,z1,z2,z44,z3,z6]),(0,[z29,z0,z1,z2,z3,z49,z6]),(0,[z0,z1,z153,z2,z3,z4,z6]),(0,[z154,z0,z1,z2,z3,z4,z6]),(0,[z155,z0,z1,z2,z3,z4,z6]),(0,[z156,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z157]),(0,[z0,z1,z11,z2,z3,z18,z6]),(1,[z0,z1,z158,z2,z3,z6]),(0,[z0,z159,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z44,z44,z3,z6]),(0,[z160,z17,z0,z1,z2,z3,z6])],[(0,[z80,z0,z1,z2,z44,z3,z6]),(0,[z133,z0,z1,z2,z44,z3,z6]),(0,[z0,z1,z2,z3,z161,z4,z6]),(0,[z0,z1,z2,z3,z87,z4,z6]),(0,[z0,z1,z2,z3,z4,z162,z6]),(0,[z0,z1,z2,z3,z14,z6,z163]),(1,[z164,z0,z1,z2,z3,z6]),(0,[z0,z1,z100,z11,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z165,z6])],[(0,[z0,z1,z2,z3,z129,z4,z6])],[(1,[z82,z0,z55,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z166,z6]),(0,[z0,z1,z2,z3,z4,z6,z167]),(0,[z0,z1,z2,z3,z18,z4,z6]),(0,[z8,z0,z1,z2,z3,z78,z6]),(0,[z0,z1,z11,z2,z3,z6,z33]),(0,[z168,z29,z0,z1,z2,z3,z6]),(0,[z17,z0,z1,z2,z3,z6,z142])],[(0,[z0,z1,z2,z3,z4,z6,z146]),(0,[z0,z36,z1,z51,z3,z4,z6]),(0,[z0,z1,z169,z2,z3,z14,z6]),(0,[z29,z0,z1,z170,z2,z3,z6]),(1,[z0,z1,z2,z3,z6,z171]),(0,[z29,z0,z1,z2,z3,z6,z142]),(0,[z0,z1,z111,z48,z2,z4,z6])]],
   [[(0,[z8,z0,z1,z2,z3,z87,z6]),(0,[z172,z0,z1,z2,z3,z4,z6]),(1,[z173,z1,z2,z3,z4,z6]),(0,[z29,z0,z1,z174,z2,z3,z6]),(1,[z0,z1,z2,z3,z6,z175]),(0,[z0,z1,z2,z44,z3,z96,z6]),(0,[z0,z1,z169,z2,z3,z6,z33])],[(0,[z0,z1,z2,z3,z176,z4,z6]),(0,[z17,z72,z0,z1,z2,z3,z6]),(0,[z133,z1,z2,z42,z3,z4,z6]),(0,[z0,z1,z2,z3,z13,z4,z6]),(1,[z0,z1,z2,z3,z177,z6]),(0,[z0,z1,z178,z2,z3,z4,z6])],[(0,[z25,z0,z1,z2,z179,z4,z6]),(0,[z0,z180,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z131,z14,z6]),(0,[z0,z1,z48,z2,z3,z14,z6]),(0,[z0,z1,z30,z2,z3,z4,z6])],[(0,[z80,z0,z1,z2,z3,z181,z6]),(0,[z0,z41,z2,z3,z4,z6,z68]),(0,[z0,z182,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z183,z3,z4,z6]),(0,[z21,z184,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z14,z6,z185]),(0,[z0,z1,z2,z3,z131,z6,z33]),(0,[z160,z8,z0,z1,z2,z3,z6]),(0,[z0,z1,z11,z2,z44,z3,z6])],[(0,[z0,z1,z2,z42,z3,z4,z6]),(0,[z94,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z186,z4,z6]),(0,[z0,z1,z2,z43,z3,z4,z6]),(0,[z0,z1,z2,z3,z187,z4,z6]),(0,[z188,z0,z1,z135,z2,z3,z6]),(0,[z29,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z189,z4,z6]),(0,[z133,z0,z1,z190,z3,z4,z6]),(0,[z0,z1,z2,z191,z3,z4,z6]),(0,[z133,z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z192,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z193]),(0,[z25,z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z194,z2,z3,z4,z6]),(0,[z0,z1,z111,z2,z3,z14,z6]),(0,[z0,z1,z2,z44,z3,z78,z6]),(0,[z0,z1,z169,z2,z44,z3,z6])],[(0,[z0,z1,z11,z2,z42,z3,z6]),(0,[z0,z1,z2,z3,z195,z4,z6]),(0,[z124,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z196,z3,z13,z4,z6]),(0,[z197,z0,z2,z3,z4,z6,z68]),(0,[z0,z1,z111,z2,z3,z6,z33]),(0,[z0,z1,z2,z3,z6,z33,z198])],[(0,[z199,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z200,z4,z6]),(0,[z23,z0,z1,z2,z3,z16,z6]),(0,[z94,z1,z2,z3,z87,z4,z6]),(0,[z0,z1,z2,z44,z3,z87,z6]),(0,[z0,z201,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z202,z14,z6]),(0,[z0,z1,z2,z3,z203,z4,z6]),(0,[z0,z1,z63,z2,z3,z4,z6])]],
   [[(0,[z72,z0,z1,z2,z3,z204,z6]),(0,[z205,z0,z1,z2,z3,z4,z6]),(0,[z0,z40,z1,z2,z3,z4,z68]),(0,[z29,z0,z1,z2,z3,z206,z6]),(0,[z0,z1,z11,z2,z3,z96,z6])],[(1,[z0,z1,z2,z207,z3,z6]),(0,[z0,z1,z2,z3,z208,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z209]),(0,[z8,z0,z1,z2,z3,z6,z142]),(0,[z210,z0,z1,z2,z3,z4,z6])],[(0,[z211,z0,z1,z2,z3,z4,z6]),(0,[z0,z40,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z26,z4,z6]),(0,[z0,z1,z2,z3,z14,z14,z6]),(0,[z0,z1,z2,z3,z4,z212,z6]),(0,[z0,z1,z111,z2,z44,z3,z6])],[(0,[z8,z72,z0,z1,z2,z3,z6]),(0,[z0,z1,z213,z2,z3,z4,z6]),(0,[z214,z0,z1,z2,z3,z4,z6]),(0,[z215,z0,z1,z2,z3,z4,z6]),(0,[z28,z8,z0,z1,z2,z3,z6])],[(0,[z216,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z217]),(0,[z25,z0,z1,z218,z3,z4,z6]),(0,[z0,z1,z219,z2,z3,z4,z6]),(0,[z0,z1,z135,z2,z3,z14,z6]),(0,[z0,z1,z11,z2,z3,z78,z6]),(0,[z0,z1,z2,z3,z69,z6,z33]),(0,[z0,z1,z220,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z78,z6,z33]),(0,[z0,z1,z2,z3,z221,z6,z33]),(0,[z0,z1,z79,z2,z3,z6,z33])],[(0,[z29,z80,z0,z1,z2,z3,z6]),(1,[z0,z1,z2,z3,z204,z6]),(0,[z222,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z6,z198]),(0,[z0,z1,z169,z2,z3,z16,z6]),(0,[z0,z1,z95,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z223,z131,z6]),(0,[z0,z1,z224,z2,z3,z4,z6]),(0,[z0,z1,z135,z2,z3,z6,z33]),(0,[z60,z0,z1,z2,z3,z4,z6]),(0,[z225,z0,z1,z2,z3,z6,z33])],[(0,[z0,z1,z2,z3,z4,z6,z226]),(0,[z20,z0,z1,z2,z227,z4,z6]),(0,[z0,z228,z1,z2,z3,z4,z6]),(0,[z0,z1,z11,z2,z3,z87,z6]),(0,[z0,z1,z2,z3,z229,z13,z6]),(1,[z149,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z96,z14,z6]),(0,[z8,z0,z1,z2,z3,z6,z230]),(0,[z0,z1,z2,z3,z4,z6,z231]),(0,[z232,z17,z0,z1,z2,z3,z6])]],
   [[(0,[z17,z133,z0,z1,z2,z3,z6]),(1,[z0,z1,z2,z3,z233,z6]),(0,[z0,z1,z234,z2,z3,z14,z6]),(1,[z0,z1,z2,z3,z6,z163]),(0,[z235,z0,z1,z2,z3,z4,z6]),(0,[z0,z236,z1,z2,z3,z4,z6]),(0,[z17,z0,z1,z11,z2,z3,z6]),(0,[z0,z237,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z44,z3,z6,z142]),(0,[z0,z1,z2,z238,z44,z3,z6]),(0,[z0,z1,z2,z3,z6,z33,z239])],[(0,[z0,z1,z2,z3,z49,z6,z33]),(0,[z0,z1,z51,z11,z2,z3,z6]),(0,[z0,z1,z2,z3,z131,z16,z6]),(0,[z0,z1,z48,z2,z3,z16,z6]),(0,[z0,z1,z240,z2,z3,z4,z6]),(0,[z0,z1,z241,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z116,z4,z6]),(0,[z0,z1,z242,z2,z3,z4,z6]),(0,[z0,z36,z1,z30,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z243,z6]),(1,[z0,z2,z3,z244,z4,z6]),(0,[z0,z1,z245,z2,z3,z4,z6])],[(0,[z94,z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z135,z2,z44,z3,z6]),(0,[z29,z0,z1,z169,z2,z3,z6]),(0,[z83,z0,z1,z2,z44,z3,z6]),(0,[z149,z17,z0,z1,z2,z3,z6])],[(0,[z184,z0,z1,z2,z3,z246,z6]),(0,[z0,z1,z2,z3,z247,z4,z6]),(0,[z0,z1,z111,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z4,z6,z248]),(0,[z0,z1,z11,z2,z3,z249,z6]),(0,[z250,z0,z1,z2,z3,z4,z6])],[(0,[z124,z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z16,z81,z6]),(0,[z82,z0,z1,z2,z3,z5,z6]),(0,[z29,z0,z1,z100,z2,z3,z6])],[(0,[z80,z0,z1,z2,z3,z4,z6]),(0,[z133,z0,z1,z2,z3,z4,z6]),(0,[z25,z0,z1,z2,z3,z4,z6]),(0,[z82,z0,z1,z11,z2,z3,z6]),(0,[z251,z0,z1,z170,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z252,z6])],[(0,[z17,z184,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z125,z4,z6]),(0,[z0,z253,z1,z2,z3,z4,z6]),(0,[z0,z254,z1,z2,z255,z4,z6]),(0,[z0,z1,z256,z2,z3,z4,z6]),(0,[z257,z0,z1,z2,z3,z4,z6]),(1,[z17,z0,z1,z2,z3,z6])]],
   [[(0,[z0,z258,z1,z2,z3,z4,z6]),(0,[z259,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z260,z2,z3,z4,z6]),(0,[z23,z0,z1,z2,z3,z4,z6]),(0,[z82,z0,z36,z2,z3,z4,z6]),(0,[z0,z261,z1,z2,z3,z4,z6]),(0,[z262,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z11,z2,z3,z6,z142]),(0,[z17,z0,z1,z135,z2,z3,z6]),(0,[z263,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z44,z3,z6,z264])],[(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z265,z4,z6]),(0,[z72,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z238,z3,z16,z6]),(0,[z0,z1,z266,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z136]),(0,[z0,z1,z2,z44,z3,z119,z6]),(0,[z0,z1,z267,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z268,z6,z33])],[(0,[z72,z0,z1,z2,z3,z6,z33]),(1,[z20,z1,z2,z49,z4,z6]),(0,[z0,z1,z2,z3,z14,z16,z6]),(0,[z117,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z269,z4,z6])],[(0,[z0,z1,z2,z3,z270,z4,z6]),(0,[z8,z133,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z271]),(0,[z0,z1,z2,z3,z4,z272,z6]),(1,[z0,z114,z2,z3,z4,z6]),(0,[z0,z1,z273,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z274,z6]),(0,[z149,z0,z1,z2,z3,z14,z6]),(0,[z8,z0,z1,z11,z2,z3,z6]),(0,[z275,z0,z1,z2,z3,z4,z6]),(0,[z276,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z135,z190,z3,z4,z6]),(0,[z277,z0,z1,z2,z3,z4,z6]),(0,[z17,z0,z1,z2,z3,z81,z6]),(0,[z0,z1,z135,z2,z3,z16,z6]),(0,[z197,z0,z1,z2,z3,z4,z206]),(0,[z0,z1,z109,z11,z2,z3,z6]),(0,[z29,z0,z1,z2,z3,z278,z6]),(0,[z0,z1,z2,z3,z4,z6,z103]),(0,[z0,z1,z2,z3,z12,z6,z103]),(0,[z0,z1,z2,z3,z279,z4,z6])],[(0,[z0,z1,z280,z2,z3,z4,z6])],[(0,[z0,z1,z281,z2,z3,z4,z6]),(0,[z0,z282,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z96,z16,z6]),(0,[z0,z1,z2,z3,z4,z6,z107]),(0,[z0,z1,z2,z3,z4,z6,z283])],[(0,[z0,z1,z2,z284,z3,z4,z6]),(0,[z72,z0,z1,z2,z44,z3,z6]),(0,[z285,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z4,z286,z6]),(0,[z0,z1,z11,z2,z3,z287,z6]),(0,[z0,z1,z11,z2,z3,z6,z136]),(0,[z0,z1,z169,z2,z3,z78,z4]),(0,[z0,z1,z169,z2,z3,z4,z6])]],
   [[(0,[z0,z126,z1,z11,z2,z3,z6]),(0,[z0,z1,z2,z288,z3,z4,z6])],[(0,[z289,z0,z1,z2,z3,z4,z6]),(0,[z20,z0,z1,z11,z2,z3,z6]),(0,[z0,z1,z2,z3,z290,z4,z6]),(1,[z291,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z292]),(0,[z0,z1,z2,z3,z4,z6,z293]),(0,[z294,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z295])],[(0,[z8,z184,z0,z1,z2,z3,z6]),(1,[z0,z1,z2,z296,z3,z6]),(0,[z17,z0,z1,z2,z55,z3,z6]),(0,[z0,z1,z297,z2,z3,z4,z6]),(0,[z0,z1,z298,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z131,z4,z6]),(0,[z299,z8,z0,z1,z2,z3,z6]),(0,[z0,z1,z11,z2,z3,z6,z103]),(0,[z0,z1,z48,z2,z3,z4,z6]),(1,[z0,z1,z2,z300,z3,z6])],[(0,[z80,z0,z1,z11,z2,z3,z6]),(0,[z301,z0,z1,z2,z3,z4,z6]),(0,[z133,z0,z1,z11,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z302,z6]),(0,[z8,z0,z1,z135,z2,z3,z6]),(0,[z0,z1,z11,z2,z303,z3,z6]),(1,[z29,z0,z1,z2,z44,z6])],[(0,[z94,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z304]),(0,[z0,z1,z2,z3,z305,z4,z6]),(0,[z0,z1,z109,z135,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z306,z6]),(1,[z0,z1,z2,z3,z279,z6])],[(0,[z0,z1,z2,z3,z13,z6,z33]),(0,[z0,z1,z170,z2,z3,z14,z6]),(0,[z0,z40,z2,z3,z4,z206,z6]),(0,[z29,z0,z1,z2,z3,z18,z6]),(0,[z0,z1,z111,z2,z3,z4,z6]),(0,[z17,z0,z1,z48,z2,z3,z6]),(0,[z17,z0,z1,z2,z3,z4,z33])],[(0,[z0,z1,z2,z3,z307,z4,z6]),(0,[z124,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z185]),(0,[z308,z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z14,z309,z6]),(0,[z0,z1,z30,z2,z3,z6,z33]),(0,[z310,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z11,z3,z18,z4,z6]),(0,[z0,z311,z1,z2,z3,z6,z33])],[(0,[z8,z0,z1,z2,z3,z81,z6]),(0,[z0,z1,z2,z3,z202,z4,z6]),(0,[z17,z0,z254,z1,z2,z3,z6])]],
   [[(0,[z72,z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z312,z4,z6]),(0,[z29,z0,z254,z1,z2,z3,z6]),(0,[z0,z1,z313,z2,z3,z16,z6]),(0,[z0,z40,z1,z2,z3,z314,z6])],[],[(0,[z0,z1,z2,z3,z4,z315,z6]),(0,[z0,z1,z2,z3,z3,z4,z6]),(0,[z0,z1,z316,z2,z3,z4,z6]),(0,[z0,z1,z2,z238,z3,z4,z6]),(0,[z0,z1,z11,z11,z2,z3,z6]),(0,[z0,z1,z2,z3,z317,z4,z6])],[(0,[z318,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z179,z4,z6]),(0,[z0,z1,z100,z30,z3,z4,z6]),(0,[z0,z1,z30,z2,z44,z3,z6])],[(0,[z319,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z320,z3,z4,z6]),(0,[z251,z0,z1,z100,z2,z4,z6]),(0,[z0,z1,z2,z3,z321,z4,z6]),(0,[z0,z1,z169,z11,z2,z3,z6])],[(1,[z0,z1,z2,z3,z246,z6]),(0,[z225,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z1,z2,z55,z3,z6]),(0,[z0,z1,z135,z2,z3,z4,z6])],[(0,[z21,z0,z1,z2,z49,z4,z6]),(0,[z0,z1,z2,z44,z3,z81,z6]),(1,[z0,z1,z2,z3,z322,z6]),(0,[z0,z1,z2,z323,z3,z4,z6]),(1,[z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z147,z2,z3,z16,z6]),(0,[z0,z40,z1,z2,z3,z6,z33]),(0,[z324,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z325,z6])],[(0,[z0,z1,z326,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z327]),(0,[z25,z0,z1,z2,z3,z4,z185]),(0,[z328,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z96,z4,z6]),(0,[z0,z1,z2,z329,z44,z3,z6]),(0,[z0,z1,z2,z3,z330,z4,z6])]],
   [[(0,[z29,z0,z1,z2,z42,z3,z6]),(0,[z21,z1,z2,z227,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z81,z6]),(0,[z0,z1,z2,z255,z3,z14,z6]),(0,[z0,z1,z234,z2,z3,z4,z6]),(0,[z0,z1,z100,z30,z2,z4,z6]),(0,[z8,z0,z1,z48,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z331,z6])],[(0,[z0,z1,z2,z3,z332,z4,z6]),(0,[z0,z1,z2,z3,z4,z333,z6]),(1,[z0,z1,z2,z3,z334,z6]),(0,[z0,z1,z2,z3,z335,z4,z6]),(1,[z336,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z44,z3,z108,z6]),(0,[z0,z1,z48,z2,z3,z4,z103])],[(1,[z0,z1,z2,z3,z73,z6]),(0,[z0,z337,z1,z2,z3,z4,z6]),(0,[z82,z0,z1,z51,z3,z4,z6]),(0,[z8,z0,z254,z1,z2,z3,z6]),(0,[z0,z1,z111,z11,z2,z3,z6]),(0,[z29,z0,z1,z2,z3,z96,z6]),(0,[z0,z338,z1,z2,z44,z3,z6])],[(0,[z72,z80,z0,z2,z3,z4,z6]),(0,[z339,z0,z1,z2,z3,z4,z6]),(0,[z0,z36,z1,z2,z3,z340,z6]),(0,[z0,z1,z2,z3,z4,z341,z6]),(0,[z0,z1,z2,z3,z16,z69,z6]),(0,[z0,z40,z1,z2,z44,z3,z6]),(0,[z17,z29,z0,z1,z2,z3,z6])],[(0,[z0,z1,z170,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z4,z6,z342]),(0,[z0,z1,z2,z3,z4,z6,z343]),(0,[z344,z0,z1,z2,z3,z4,z6])],[(0,[z345,z0,z1,z2,z3,z4,z6]),(0,[z172,z1,z2,z3,z4,z6,z68]),(0,[z0,z1,z2,z3,z4,z38,z6])],[(0,[z80,z0,z1,z2,z3,z120,z6]),(1,[z0,z1,z218,z3,z4,z6]),(0,[z25,z0,z1,z2,z3,z4,z81]),(0,[z0,z1,z11,z2,z3,z81,z6]),(0,[z346,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z347,z2,z3,z4,z6]),(1,[z94,z1,z2,z3,z87,z6]),(0,[z0,z1,z2,z348,z3,z4,z6]),(0,[z349,z0,z1,z2,z3,z16,z6]),(0,[z308,z0,z1,z2,z3,z4,z6]),(0,[z197,z0,z1,z2,z3,z177,z6]),(0,[z29,z0,z1,z2,z3,z78,z6]),(0,[z350,z17,z0,z1,z2,z3,z6])]],
   [[(0,[z0,z1,z351,z2,z3,z4,z6]),(0,[z352,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z353,z2,z3,z4,z6]),(0,[z17,z0,z1,z2,z3,z13,z6]),(0,[z0,z354,z1,z2,z3,z4,z6]),(0,[z0,z1,z100,z2,z3,z335,z6]),(0,[z0,z1,z2,z3,z355,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z356])],[(0,[z72,z0,z1,z2,z3,z4,z6]),(0,[z0,z357,z1,z2,z3,z4,z6]),(0,[z29,z0,z1,z2,z3,z87,z6]),(0,[z358,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z313,z2,z3,z4,z6]),(0,[z8,z310,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z45,z4,z6])],[(0,[z0,z1,z359,z2,z3,z4,z6]),(0,[z25,z0,z1,z2,z3,z6,z33]),(0,[z117,z0,z1,z2,z3,z4,z6]),(0,[z251,z0,z1,z2,z13,z4,z6]),(1,[z1,z2,z3,z4,z6,z248]),(0,[z360,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z135,z11,z2,z3,z6]),(0,[z17,z0,z1,z2,z3,z69,z6]),(0,[z263,z0,z1,z48,z2,z3,z6])],[(0,[z0,z1,z2,z3,z4,z361,z6]),(0,[z0,z1,z2,z362,z3,z4,z6]),(0,[z0,z1,z2,z363,z3,z4,z6]),(0,[z149,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z90,z11,z2,z3,z6]),(1,[z0,z1,z174,z2,z3,z6]),(0,[z0,z1,z364,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z365,z4,z6])],[(0,[z21,z0,z1,z2,z3,z233,z6]),(0,[z23,z0,z1,z2,z3,z6,z33]),(0,[z0,z1,z366,z2,z3,z4,z6]),(0,[z0,z1,z11,z2,z55,z3,z6]),(0,[z0,z1,z63,z2,z3,z367,z6]),(0,[z0,z1,z2,z3,z6,z368,z33]),(0,[z17,z0,z1,z2,z3,z6,z6])],[(0,[z184,z1,z2,z3,z49,z4,z6]),(0,[z124,z1,z2,z3,z4,z81,z6]),(0,[z369,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z370,z2,z3,z4,z6]),(0,[z0,z1,z170,z2,z131,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z371]),(0,[z0,z254,z1,z170,z2,z4,z6]),(0,[z0,z1,z2,z3,z14,z6,z372]),(0,[z17,z0,z40,z1,z2,z3,z6]),(0,[z8,z29,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z373,z6]),(0,[z0,z1,z63,z2,z3,z212,z6]),(0,[z0,z1,z2,z3,z69,z58,z6]),(0,[z0,z1,z2,z3,z4,z6,z374])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z375,z3,z4,z6]),(0,[z17,z0,z1,z190,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z376]),(0,[z25,z0,z1,z2,z44,z3,z6]),(0,[z124,z0,z1,z2,z3,z4,z185]),(0,[z0,z1,z147,z2,z3,z4,z6]),(0,[z0,z1,z2,z255,z3,z16,z6]),(0,[z0,z1,z377,z2,z3,z4,z6]),(0,[z0,z118,z1,z2,z3,z4,z6]),(0,[z0,z1,z378,z2,z3,z6,z33])]],
   [[(0,[z0,z1,z190,z2,z3,z14,z6]),(0,[z0,z379,z1,z2,z3,z4,z6]),(0,[z0,z380,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z381,z6])],[(0,[z0,z1,z190,z2,z3,z6,z33]),(0,[z0,z1,z2,z3,z4,z382,z6]),(0,[z23,z0,z1,z2,z44,z3,z6]),(0,[z0,z36,z1,z170,z3,z4,z6]),(0,[z0,z1,z2,z3,z16,z6,z136]),(1,[z57,z0,z1,z2,z3,z6]),(0,[z0,z1,z383,z2,z3,z4,z6])],[(0,[z384,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z385]),(0,[z17,z94,z0,z1,z2,z3,z6]),(0,[z386,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z111,z2,z3,z110,z6])],[(0,[z86,z0,z41,z2,z3,z4,z6]),(0,[z251,z0,z1,z2,z3,z14,z6]),(0,[z8,z0,z1,z2,z3,z13,z6]),(1,[z0,z1,z377,z2,z3,z6])],[(0,[z251,z0,z1,z2,z3,z6,z33]),(0,[z0,z1,z2,z3,z16,z6,z103]),(0,[z57,z0,z1,z170,z2,z3,z6]),(0,[z0,z1,z378,z2,z44,z3,z6])],[(0,[z29,z72,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z387]),(0,[z82,z0,z1,z30,z3,z4,z6]),(0,[z0,z36,z1,z2,z3,z66,z6]),(0,[z0,z311,z1,z2,z3,z4,z6]),(0,[z0,z1,z170,z2,z3,z4,z6]),(0,[z8,z0,z1,z2,z3,z69,z6]),(1,[z0,z1,z109,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z388]),(0,[z0,z1,z389,z2,z3,z4,z6])],[(0,[z0,z1,z390,z2,z3,z4,z6]),(0,[z0,z1,z190,z2,z44,z3,z6]),(0,[z17,z0,z1,z2,z227,z3,z6]),(0,[z124,z0,z1,z2,z3,z4,z81]),(0,[z0,z1,z391,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z16,z6,z107]),(0,[z160,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z177,z4,z6]),(0,[z0,z1,z2,z3,z4,z127,z6]),(0,[z0,z1,z48,z2,z3,z6,z33])],[(0,[z29,z0,z1,z2,z227,z3,z6]),(0,[z28,z17,z0,z1,z2,z3,z6]),(0,[z160,z0,z1,z2,z3,z6,z33])]],
   [[(0,[z349,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z392]),(0,[z0,z1,z2,z3,z393,z4,z6]),(0,[z94,z0,z1,z2,z3,z6,z33]),(0,[z0,z1,z2,z3,z394,z4,z6]),(0,[z0,z1,z2,z3,z395,z4,z6]),(0,[z17,z0,z1,z2,z3,z6,z136])],[(0,[z86,z0,z1,z2,z3,z14,z6]),(0,[z184,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z329,z3,z4,z6]),(0,[z0,z1,z396,z2,z3,z4,z6]),(0,[z251,z0,z1,z2,z44,z3,z6]),(0,[z8,z0,z40,z1,z2,z3,z6]),(0,[z57,z0,z1,z2,z3,z4,z6]),(1,[z8,z0,z1,z11,z3,z6]),(0,[z188,z8,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z397]),(0,[z29,z0,z1,z2,z3,z6,z136]),(0,[z0,z1,z398,z2,z3,z4,z6]),(0,[z0,z399,z1,z2,z3,z4,z6]),(0,[z0,z1,z400,z2,z3,z6,z33])],[(0,[z184,z0,z1,z2,z3,z6,z33]),(0,[z8,z0,z1,z190,z2,z3,z6]),(0,[z25,z0,z1,z2,z3,z104,z6]),(0,[z0,z1,z2,z3,z4,z401,z6]),(0,[z124,z0,z1,z2,z3,z6,z33]),(0,[z0,z1,z2,z44,z3,z13,z6]),(0,[z0,z1,z63,z2,z3,z4,z69])],[(0,[z21,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z16,z6,z402]),(0,[z0,z1,z48,z2,z44,z3,z6]),(0,[z17,z0,z1,z2,z3,z6,z103]),(0,[z0,z1,z2,z3,z6,z6,z33])],[(1,[z65,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z44,z3,z69,z6]),(0,[z29,z0,z1,z2,z3,z3,z6]),(0,[z29,z0,z1,z2,z3,z6,z103]),(0,[z160,z0,z1,z2,z44,z3,z6]),(0,[z0,z338,z1,z2,z3,z4,z6])],[(0,[z0,z403,z1,z2,z3,z4,z6]),(0,[z23,z0,z1,z2,z3,z87,z6]),(0,[z8,z94,z0,z1,z2,z3,z6]),(0,[z94,z0,z1,z2,z44,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z404]),(0,[z0,z1,z2,z3,z244,z4,z6]),(1,[z405,z0,z1,z2,z3,z6]),(0,[z17,z0,z1,z2,z3,z6,z107]),(0,[z0,z406,z1,z2,z3,z4,z6])],[(0,[z0,z1,z407,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z16,z6,z185]),(0,[z0,z1,z2,z408,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z67,z6]),(0,[z0,z1,z2,z3,z4,z6,z68]),(0,[z29,z0,z1,z2,z3,z6,z107]),(0,[z0,z1,z2,z3,z4,z69,z6]),(0,[z0,z409,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z78,z4,z33])],[(0,[z184,z0,z1,z2,z44,z3,z6]),(0,[z0,z1,z190,z2,z3,z16,z6]),(0,[z124,z0,z1,z2,z44,z3,z6]),(0,[z0,z1,z2,z55,z3,z14,z6]),(0,[z291,z0,z1,z2,z3,z13,z6]),(0,[z28,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z14,z6,z33]),(0,[z0,z1,z2,z3,z4,z6,z410])]],
   [[(0,[z0,z1,z411,z2,z3,z4,z6]),(0,[z412,z0,z1,z2,z3,z4,z6]),(0,[z72,z1,z2,z3,z4,z81,z6]),(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z0,z1,z2,z413,z3,z4,z6]),(0,[z0,z1,z2,z55,z3,z6,z33]),(0,[z0,z1,z2,z255,z3,z4,z6]),(0,[z17,z414,z0,z1,z2,z3,z6])],[(0,[z415,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z1,z2,z227,z3,z6]),(0,[z1,z2,z3,z4,z81,z6,z185]),(0,[z0,z1,z2,z3,z4,z6,z171]),(0,[z0,z1,z416,z2,z3,z4,z6])],[(0,[z251,z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z11,z2,z3,z13,z6]),(0,[z0,z1,z2,z3,z16,z315,z6]),(0,[z0,z1,z2,z3,z4,z417,z6]),(0,[z0,z1,z30,z11,z2,z3,z6]),(0,[z418,z29,z0,z1,z2,z3,z6]),(0,[z419,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z175]),(0,[z420,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z421]),(0,[z0,z422,z1,z2,z3,z4,z6]),(0,[z8,z0,z1,z2,z3,z6,z136]),(0,[z0,z1,z2,z3,z96,z6,z33])],[(0,[z0,z1,z2,z423,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z424,z6]),(0,[z0,z1,z2,z425,z3,z4,z6]),(0,[z29,z133,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z426,z4,z6]),(0,[z0,z1,z2,z3,z427,z4,z6]),(0,[z0,z254,z1,z100,z2,z4,z6]),(0,[z173,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z9,z3,z6]),(0,[z0,z1,z11,z2,z3,z69,z6]),(0,[z29,z0,z1,z11,z2,z3,z6])],[(0,[z0,z1,z2,z3,z428,z4,z6]),(0,[z17,z0,z1,z2,z3,z6,z185]),(0,[z0,z1,z2,z55,z44,z3,z6]),(0,[z0,z1,z2,z3,z4,z429,z6]),(0,[z160,z0,z1,z2,z3,z16,z6]),(0,[z197,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z4,z6,z430])],[(0,[z21,z1,z2,z42,z3,z4,z6]),(0,[z197,z0,z1,z2,z3,z6,z33]),(0,[z8,z0,z1,z2,z3,z6,z103]),(0,[z0,z1,z2,z3,z4,z431,z6])],[(0,[z0,z1,z63,z11,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z432,z6]),(0,[z0,z1,z2,z3,z4,z433,z6])]],
   [[(0,[z86,z0,z1,z2,z3,z16,z6]),(0,[z434,z0,z1,z2,z3,z4,z6]),(0,[z184,z0,z1,z190,z3,z4,z6]),(0,[z184,z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z435,z4,z6]),(0,[z0,z1,z2,z3,z166,z16,z6]),(0,[z0,z1,z2,z3,z4,z6,z436]),(0,[z8,z0,z1,z2,z3,z6,z107]),(1,[z0,z1,z2,z3,z437,z6]),(0,[z0,z1,z438,z2,z3,z4,z6])],[(0,[z134,z0,z1,z2,z3,z4,z6]),(0,[z94,z0,z1,z2,z3,z87,z6]),(0,[z336,z0,z1,z2,z3,z69,z6])],[(0,[z21,z0,z1,z2,z3,z16,z6]),(0,[z0,z40,z1,z11,z2,z3,z6]),(0,[z0,z1,z100,z170,z3,z4,z6]),(0,[z0,z1,z2,z44,z3,z6,z136]),(0,[z0,z1,z439,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z440])],[(0,[z29,z184,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z441]),(0,[z0,z1,z2,z3,z4,z24,z6]),(0,[z0,z1,z2,z3,z4,z6,z442]),(0,[z197,z0,z1,z2,z44,z3,z6]),(0,[z17,z197,z0,z1,z2,z3,z6]),(0,[z8,z0,z1,z2,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z33,z33]),(1,[z0,z1,z443,z2,z3,z6])],[(0,[z444,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z445,z2,z3,z4,z6]),(0,[z0,z1,z2,z446,z3,z4,z6]),(0,[z447,z0,z1,z2,z3,z4,z6]),(0,[z29,z0,z1,z135,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z33,z448]),(0,[z449,z17,z0,z1,z2,z3,z6]),(0,[z17,z0,z1,z2,z450,z3,z6])],[(0,[z17,z86,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z451,z6]),(0,[z17,z124,z0,z1,z2,z3,z6]),(1,[z0,z1,z2,z3,z314,z6]),(0,[z17,z8,z0,z1,z2,z3,z6]),(0,[z29,z210,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z44,z3,z3,z6]),(0,[z0,z1,z2,z44,z3,z6,z103])],[(0,[z0,z1,z2,z55,z3,z16,z6]),(0,[z28,z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z452,z4,z6]),(0,[z0,z1,z2,z3,z437,z6,z136]),(0,[z0,z1,z378,z2,z3,z4,z6])],[(0,[z453,z0,z1,z2,z3,z4,z6]),(0,[z454,z0,z1,z2,z3,z4,z6]),(1,[z117,z0,z1,z2,z3,z6]),(0,[z0,z455,z1,z2,z3,z4,z6]),(0,[z168,z0,z1,z2,z255,z3,z6]),(0,[z0,z1,z2,z44,z3,z6,z107])]],
   [[(0,[z0,z1,z2,z3,z4,z204,z6]),(0,[z0,z1,z190,z2,z3,z4,z6]),(0,[z0,z1,z11,z2,z227,z3,z6]),(0,[z0,z1,z48,z2,z227,z4,z6]),(0,[z8,z0,z1,z2,z3,z6,z185]),(0,[z29,z0,z1,z2,z3,z81,z6]),(0,[z0,z1,z2,z3,z4,z6,z198]),(0,[z0,z1,z2,z3,z223,z4,z6]),(0,[z0,z236,z1,z11,z2,z3,z6]),(0,[z0,z1,z2,z456,z3,z4,z6]),(0,[z457,z0,z1,z2,z3,z4,z6]),(0,[z17,z0,z458,z1,z2,z3,z6]),(0,[z17,z0,z1,z2,z300,z3,z6])],[(0,[z25,z80,z1,z2,z3,z4,z6]),(0,[z1,z2,z227,z3,z49,z4,z6]),(0,[z0,z254,z2,z255,z3,z4,z6]),(1,[z0,z1,z234,z2,z3,z6]),(0,[z0,z1,z2,z459,z3,z4,z6])],[(1,[z0,z1,z2,z3,z192,z6]),(0,[z0,z1,z2,z460,z3,z4,z6]),(0,[z0,z1,z461,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z233,z6]),(1,[z0,z1,z2,z3,z462,z6]),(0,[z0,z1,z463,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z163]),(1,[z263,z0,z1,z2,z3,z6])],[(0,[z251,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z6,z33])],[(1,[z80,z41,z2,z3,z4,z6]),(0,[z72,z0,z40,z2,z3,z4,z6]),(0,[z0,z1,z464,z2,z3,z4,z6]),(0,[z465,z0,z1,z2,z3,z4,z6]),(0,[z197,z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z279,z6,z103]),(0,[z0,z1,z2,z3,z309,z6,z33]),(0,[z0,z1,z2,z3,z325,z6,z33])],[(1,[z133,z1,z42,z3,z4,z6]),(0,[z17,z0,z36,z1,z2,z3,z6]),(0,[z0,z1,z466,z2,z3,z4,z6]),(0,[z17,z0,z1,z111,z2,z3,z6])],[(0,[z160,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z218,z3,z4,z6]),(0,[z25,z1,z2,z3,z4,z6,z185]),(0,[z25,z0,z1,z11,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z402]),(0,[z29,z0,z1,z2,z55,z3,z6]),(0,[z0,z467,z1,z2,z3,z4,z6]),(0,[z29,z0,z36,z1,z2,z3,z6]),(1,[z468,z0,z1,z2,z3,z6]),(0,[z8,z197,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z469,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z470]),(0,[z471,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z472,z2,z3,z4,z6]),(0,[z0,z1,z2,z473,z3,z4,z6]),(0,[z0,z1,z2,z44,z3,z6,z185]),(0,[z0,z254,z1,z2,z3,z274,z6]),(0,[z474,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z11,z2,z3,z6,z107]),(0,[z475,z0,z1,z2,z3,z4,z6]),(0,[z123,z29,z0,z1,z2,z3,z6]),(1,[z476,z0,z1,z2,z3,z6])]],
   [[(0,[z8,z86,z0,z1,z2,z3,z6]),(0,[z133,z0,z1,z42,z3,z4,z6]),(0,[z477,z0,z1,z2,z3,z4,z6]),(0,[z23,z0,z1,z11,z2,z3,z6]),(0,[z8,z124,z0,z1,z2,z3,z6]),(1,[z360,z0,z2,z3,z4,z6]),(0,[z8,z8,z0,z1,z2,z3,z6]),(1,[z0,z1,z2,z44,z3,z6]),(1,[z0,z1,z111,z2,z4,z103]),(0,[z0,z1,z400,z2,z3,z4,z6])],[(0,[z86,z0,z1,z2,z3,z4,z6]),(0,[z184,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z14,z6,z142]),(0,[z0,z1,z170,z2,z3,z6,z33]),(0,[z447,z0,z1,z11,z2,z3,z6]),(0,[z29,z0,z1,z48,z2,z3,z6])],[(0,[z25,z0,z1,z2,z3,z50,z6]),(0,[z0,z1,z11,z2,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z478,z6])],[(0,[z479,z0,z1,z2,z3,z4,z6]),(0,[z21,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z81,z6,z33]),(0,[z168,z0,z1,z2,z3,z14,z6]),(1,[z0,z1,z2,z3,z480,z6])],[(0,[z481,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z482,z2,z3,z4,z6]),(0,[z0,z1,z74,z170,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z483])],[(0,[z0,z1,z190,z11,z2,z3,z6]),(1,[z0,z1,z2,z3,z125,z6]),(0,[z0,z1,z2,z3,z4,z274,z6]),(0,[z17,z0,z484,z1,z2,z3,z6])],[(0,[z0,z1,z42,z3,z4,z6,z136]),(0,[z0,z1,z485,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z14,z4,z6]),(0,[z0,z1,z170,z2,z44,z3,z6]),(0,[z0,z1,z63,z3,z4,z6,z136])],[(1,[z0,z1,z2,z3,z181,z6]),(0,[z0,z486,z1,z2,z3,z4,z6]),(1,[z23,z1,z2,z3,z24,z6]),(0,[z0,z1,z11,z2,z3,z6,z185]),(0,[z0,z1,z2,z55,z3,z4,z6]),(0,[z28,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z63,z3,z4,z136])]],
   [[(0,[z487,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z24,z16,z6]),(0,[z0,z1,z2,z3,z4,z488,z6]),(0,[z0,z1,z2,z296,z3,z4,z6]),(0,[z8,z0,z36,z1,z2,z3,z6]),(0,[z8,z0,z1,z111,z2,z3,z6]),(0,[z0,z1,z2,z3,z489,z4,z6]),(0,[z0,z1,z135,z2,z3,z4,z69]),(0,[z0,z1,z2,z3,z4,z6,z490])],[(0,[z0,z1,z2,z3,z4,z491,z6]),(0,[z0,z1,z2,z3,z4,z6,z492]),(0,[z0,z1,z297,z3,z13,z4,z6]),(0,[z17,z0,z126,z1,z2,z3,z6]),(0,[z0,z1,z74,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z221,z6])],[(0,[z0,z1,z2,z3,z493,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z494]),(0,[z29,z0,z126,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z14,z206,z6]),(0,[z495,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z30,z3,z131,z4,z6]),(0,[z0,z1,z2,z3,z4,z496,z6]),(0,[z0,z1,z48,z11,z2,z3,z6])],[(0,[z497,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z73,z4,z6]),(1,[z0,z1,z2,z3,z104,z6]),(0,[z0,z36,z1,z2,z3,z14,z6]),(1,[z0,z1,z2,z3,z498,z6]),(0,[z197,z0,z1,z2,z3,z4,z68]),(0,[z499,z0,z1,z2,z3,z4,z6]),(0,[z301,z0,z1,z11,z2,z3,z6]),(0,[z160,z0,z1,z11,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z500,z6])],[(0,[z0,z1,z2,z3,z4,z501,z6]),(0,[z94,z0,z1,z11,z2,z3,z6]),(0,[z82,z0,z1,z170,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z340,z6]),(0,[z0,z1,z196,z2,z3,z4,z6]),(0,[z0,z1,z2,z255,z3,z6,z33]),(0,[z0,z1,z502,z2,z3,z4,z6]),(0,[z0,z1,z503,z2,z3,z4,z6])],[(0,[z504,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z505,z4,z6]),(0,[z28,z0,z2,z3,z4,z16,z6]),(0,[z197,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z506,z2,z3,z4,z6]),(0,[z507,z8,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z33,z142])],[(0,[z184,z0,z1,z11,z2,z3,z6]),(0,[z76,z0,z1,z2,z3,z4,z6]),(0,[z124,z0,z1,z11,z2,z3,z6]),(0,[z251,z0,z1,z2,z3,z62,z6]),(0,[z0,z1,z2,z3,z498,z4,z6]),(0,[z0,z1,z2,z3,z16,z6,z68]),(0,[z0,z1,z2,z3,z4,z6,z508]),(0,[z0,z1,z2,z509,z3,z4,z6]),(0,[z0,z1,z2,z96,z4,z6,z142]),(0,[z420,z0,z1,z2,z3,z6,z33])],[(0,[z0,z1,z41,z2,z3,z14,z6]),(0,[z25,z0,z510,z2,z3,z4,z6]),(0,[z251,z0,z254,z2,z3,z4,z6]),(1,[z168,z0,z1,z2,z3,z6]),(0,[z468,z0,z1,z2,z3,z16,z6]),(0,[z405,z0,z1,z2,z3,z131,z6]),(0,[z29,z29,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z511,z6])]],
   [[(0,[z0,z1,z41,z2,z3,z6,z33]),(0,[z0,z1,z2,z3,z512,z4,z6]),(0,[z513,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z514,z2,z3,z4,z6])],[(0,[z0,z1,z515,z2,z3,z4,z6]),(0,[z27,z0,z1,z2,z3,z4,z6]),(0,[z17,z0,z1,z51,z2,z3,z6]),(0,[z0,z1,z2,z255,z44,z3,z6]),(1,[z0,z1,z2,z3,z516,z6])],[(0,[z0,z1,z2,z3,z4,z6,z517]),(0,[z0,z254,z1,z2,z3,z322,z6]),(0,[z8,z0,z1,z3,z4,z6,z107]),(0,[z232,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z518,z2,z3,z4,z6]),(0,[z0,z1,z2,z227,z3,z14,z6]),(0,[z0,z1,z2,z519,z3,z4,z6]),(0,[z0,z1,z520,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z521,z14,z6]),(0,[z522,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z523,z2,z3,z4,z6]),(0,[z29,z0,z1,z2,z3,z13,z6]),(0,[z8,z0,z126,z1,z2,z3,z6]),(0,[z1,z2,z3,z4,z6,z248,z68]),(0,[z0,z1,z11,z2,z524,z3,z6]),(0,[z0,z1,z2,z525,z3,z4,z6]),(1,[z17,z0,z1,z2,z3,z33])],[(0,[z0,z1,z41,z2,z44,z3,z6]),(0,[z0,z1,z526,z2,z3,z4,z6]),(0,[z17,z0,z1,z2,z3,z6,z68]),(0,[z0,z527,z1,z2,z3,z4,z6]),(0,[z29,z0,z1,z158,z2,z3,z6]),(1,[z0,z1,z416,z2,z3,z6])],[(0,[z0,z1,z2,z3,z528,z14,z6]),(0,[z29,z0,z1,z2,z3,z6,z68]),(0,[z29,z0,z1,z2,z3,z69,z6]),(0,[z0,z529,z1,z2,z3,z4,z6]),(0,[z0,z1,z111,z2,z3,z269,z6])],[(0,[z530,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z135,z42,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z246,z6]),(0,[z0,z1,z2,z3,z4,z6,z531]),(0,[z0,z1,z532,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z34])]],
   [[(0,[z0,z1,z2,z3,z4,z16,z6]),(0,[z0,z1,z2,z3,z206,z6,z33]),(0,[z173,z1,z170,z2,z3,z4,z6]),(0,[z29,z0,z1,z2,z509,z3,z6]),(0,[z0,z1,z378,z48,z2,z3,z6]),(0,[z88,z17,z0,z1,z2,z3,z6])],[(0,[z0,z1,z533,z2,z3,z4,z6]),(0,[z0,z1,z534,z2,z3,z4,z6]),(0,[z0,z126,z2,z3,z14,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z535]),(0,[z536,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z537,z2,z3,z4,z6])],[(0,[z0,z36,z1,z2,z3,z16,z6]),(0,[z0,z1,z2,z538,z3,z4,z6]),(0,[z197,z0,z1,z11,z2,z3,z6]),(0,[z29,z0,z40,z1,z2,z3,z6]),(0,[z1,z170,z298,z2,z3,z4,z6]),(0,[z0,z1,z111,z2,z3,z4,z309])],[(0,[z29,z0,z1,z190,z2,z3,z6]),(1,[z0,z1,z196,z3,z4,z6]),(0,[z0,z1,z539,z2,z3,z4,z6]),(1,[z0,z1,z2,z43,z3,z6]),(0,[z0,z1,z2,z3,z4,z334,z6]),(1,[z0,z1,z2,z3,z6,z230]),(0,[z0,z1,z3,z4,z69,z6,z136]),(0,[z0,z1,z540,z2,z3,z4,z6]),(0,[z0,z1,z2,z300,z3,z4,z6])],[(0,[z449,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z1,z51,z2,z3,z6]),(0,[z0,z541,z1,z2,z3,z4,z6]),(0,[z0,z1,z48,z2,z4,z309,z6]),(0,[z188,z17,z0,z1,z2,z3,z6])],[(0,[z542,z0,z1,z2,z3,z4,z6]),(0,[z71,z8,z0,z1,z2,z3,z6]),(0,[z299,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z543,z6]),(0,[z345,z0,z1,z11,z2,z3,z6]),(0,[z0,z1,z2,z3,z544,z4,z6]),(1,[z0,z1,z2,z3,z6,z264])],[(0,[z0,z1,z41,z2,z3,z16,z6]),(0,[z17,z0,z1,z41,z2,z3,z6]),(1,[z0,z1,z2,z3,z545,z6]),(0,[z0,z1,z2,z3,z4,z546,z6]),(0,[z29,z94,z0,z1,z2,z3,z6]),(0,[z65,z0,z1,z2,z3,z4,z6]),(0,[z405,z0,z1,z2,z3,z4,z6])],[(0,[z474,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z547,z6]),(0,[z164,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z44,z3,z129,z6])]],
   [[(0,[z0,z1,z2,z3,z548,z4,z6]),(0,[z549,z0,z1,z2,z3,z4,z6]),(0,[z550,z0,z1,z2,z3,z4,z6]),(0,[z551,z0,z1,z2,z3,z4,z6]),(0,[z552,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z16,z6,z198]),(0,[z468,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z1,z2,z3,z6,z68]),(1,[z0,z1,z2,z3,z335,z6]),(1,[z0,z1,z2,z303,z3,z6]),(1,[z0,z1,z400,z2,z3,z6])],[(0,[z72,z0,z1,z11,z2,z3,z6]),(1,[z553,z0,z1,z2,z3,z6]),(0,[z1,z2,z3,z87,z4,z24,z6]),(0,[z25,z29,z0,z1,z2,z3,z6]),(0,[z0,z554,z1,z2,z3,z4,z6]),(0,[z555,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z322,z4,z6]),(1,[z556,z0,z1,z2,z3,z6]),(0,[z0,z1,z557,z2,z3,z4,z6])],[(0,[z0,z1,z558,z2,z3,z4,z6]),(0,[z0,z1,z2,z227,z3,z16,z6]),(0,[z17,z0,z1,z2,z3,z24,z6]),(1,[z0,z1,z147,z2,z3,z6]),(0,[z0,z1,z2,z3,z559,z4,z6])],[(0,[z23,z29,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z560]),(0,[z168,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z561,z2,z3,z4,z6]),(0,[z164,z0,z1,z2,z3,z206,z6]),(1,[z1,z298,z2,z3,z4,z6]),(0,[z8,z0,z1,z11,z3,z4,z6]),(0,[z263,z29,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z181,z4,z6]),(0,[z184,z0,z1,z2,z3,z192,z6]),(0,[z0,z1,z562,z2,z3,z4,z6]),(0,[z17,z0,z1,z30,z2,z3,z6]),(0,[z8,z0,z1,z377,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z309,z6]),(0,[z0,z1,z563,z2,z3,z4,z6])],[(0,[z86,z0,z1,z2,z3,z6,z33]),(0,[z0,z1,z2,z227,z4,z6,z103]),(0,[z82,z251,z0,z2,z3,z4,z6]),(0,[z0,z564,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z565,z4,z6]),(0,[z0,z1,z2,z3,z6,z68,z198]),(0,[z566,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z567,z6]),(0,[z0,z1,z2,z450,z3,z4,z6])],[(0,[z21,z0,z1,z2,z3,z462,z6]),(0,[z568,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z569,z3,z4,z6]),(0,[z0,z1,z2,z3,z570,z4,z6]),(0,[z0,z1,z466,z2,z44,z3,z6])],[(0,[z21,z0,z1,z2,z3,z6,z33]),(0,[z0,z1,z2,z44,z3,z6,z68]),(0,[z0,z1,z571,z2,z3,z4,z6]),(1,[z0,z1,z11,z2,z3,z6]),(0,[z0,z1,z147,z11,z2,z3,z6])]],
   [[(0,[z0,z1,z572,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z573,z6]),(0,[z0,z1,z10,z2,z3,z4,z6])],[(0,[z8,z0,z1,z41,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z4,z6]),(1,[z0,z1,z2,z3,z37,z6]),(0,[z0,z1,z2,z3,z12,z4,z6])],[(0,[z86,z0,z1,z2,z44,z3,z6])],[(1,[z0,z1,z2,z3,z50,z6]),(0,[z0,z36,z1,z2,z3,z4,z6]),(0,[z0,z36,z1,z55,z3,z4,z6]),(0,[z0,z1,z2,z574,z3,z4,z6]),(0,[z28,z0,z1,z2,z3,z6,z33])],[(0,[z80,z1,z41,z2,z3,z4,z6]),(0,[z20,z0,z1,z2,z49,z4,z6]),(0,[z21,z0,z1,z2,z44,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z575]),(0,[z17,z0,z1,z2,z255,z3,z6]),(0,[z141,z8,z0,z1,z2,z3,z6]),(1,[z0,z1,z2,z3,z58,z6]),(0,[z294,z29,z0,z1,z2,z3,z6])],[(0,[z8,z0,z1,z2,z3,z24,z6]),(0,[z0,z1,z576,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z62,z6]),(0,[z0,z1,z2,z3,z577,z16,z6]),(0,[z0,z1,z2,z3,z4,z577,z6]),(0,[z0,z1,z170,z11,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z578,z6])],[(0,[z0,z1,z390,z11,z2,z3,z6]),(0,[z0,z1,z579,z2,z3,z4,z6])],[(0,[z0,z1,z580,z2,z3,z4,z6]),(0,[z0,z1,z41,z2,z3,z4,z6]),(0,[z17,z20,z0,z1,z2,z3,z6]),(0,[z251,z0,z1,z2,z3,z498,z6]),(0,[z17,z251,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z229,z4,z6]),(0,[z0,z1,z11,z2,z3,z6,z68]),(0,[z8,z0,z1,z30,z2,z3,z6]),(0,[z0,z484,z1,z2,z3,z4,z6])]],
   [[(0,[z25,z72,z1,z2,z3,z4,z6]),(0,[z0,z1,z581,z2,z3,z4,z6]),(0,[z28,z0,z1,z2,z44,z3,z6]),(0,[z0,z1,z2,z3,z14,z6,z167]),(0,[z582,z0,z1,z2,z3,z4,z6]),(0,[z17,z17,z0,z1,z2,z3,z6])],[(0,[z0,z1,z583,z2,z3,z4,z6]),(0,[z29,z0,z1,z2,z3,z6,z185]),(0,[z0,z1,z2,z3,z4,z6,z584])],[(0,[z585,z0,z1,z2,z3,z4,z6]),(0,[z0,z586,z1,z2,z3,z4,z6]),(0,[z86,z72,z0,z2,z3,z4,z6]),(0,[z587,z0,z1,z2,z3,z4,z6]),(0,[z588,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z545,z49,z6]),(0,[z0,z1,z2,z589,z3,z4,z6]),(0,[z0,z1,z11,z2,z3,z6,z171]),(0,[z0,z1,z2,z3,z367,z4,z6]),(0,[z0,z1,z74,z2,z44,z3,z6])],[(0,[z0,z1,z2,z3,z521,z4,z6]),(0,[z0,z1,z2,z3,z4,z590,z6]),(0,[z0,z1,z2,z3,z4,z92,z6]),(0,[z0,z1,z30,z2,z3,z591,z6])],[(0,[z0,z1,z2,z44,z3,z24,z6]),(0,[z82,z0,z2,z255,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z592]),(0,[z17,z0,z1,z169,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z593,z6]),(0,[z594,z0,z1,z2,z3,z4,z6]),(0,[z23,z1,z2,z3,z4,z24,z6]),(0,[z0,z1,z2,z3,z595,z4,z6]),(0,[z0,z1,z1,z2,z3,z14,z6])],[(0,[z0,z1,z2,z596,z3,z4,z6]),(0,[z0,z1,z2,z3,z528,z4,z6]),(0,[z0,z1,z100,z2,z3,z334,z6])],[(1,[z0,z1,z297,z3,z4,z6]),(0,[z8,z0,z1,z2,z255,z3,z6]),(0,[z29,z197,z0,z1,z2,z3,z6]),(0,[z360,z0,z2,z3,z131,z4,z6]),(1,[z0,z1,z39,z2,z3,z6]),(1,[z0,z1,z2,z3,z110,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z597,z6]),(0,[z598,z0,z1,z2,z3,z4,z6]),(1,[z0,z510,z2,z3,z4,z6]),(0,[z17,z0,z1,z2,z3,z14,z6]),(0,[z197,z0,z40,z2,z3,z4,z6]),(0,[z599,z0,z1,z2,z3,z4,z6])],[(0,[z29,z86,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z207,z42,z3,z6]),(0,[z0,z1,z2,z600,z3,z4,z6]),(0,[z29,z124,z0,z1,z2,z3,z6]),(0,[z0,z1,z51,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z4,z601,z6]),(0,[z0,z1,z602,z2,z44,z3,z6])],[(1,[z0,z1,z2,z3,z120,z6]),(0,[z8,z20,z0,z1,z2,z3,z6]),(0,[z350,z0,z1,z2,z3,z4,z6]),(0,[z8,z251,z0,z1,z2,z3,z6]),(1,[z0,z1,z170,z131,z4,z6]),(0,[z29,z0,z1,z2,z44,z4,z6])],[(0,[z0,z1,z2,z3,z14,z87,z6]),(1,[z25,z1,z2,z3,z4,z185]),(0,[z603,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z604]),(0,[z0,z1,z605,z2,z3,z4,z6])],[(0,[z0,z1,z606,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z545,z4,z6]),(0,[z0,z1,z11,z2,z3,z24,z6]),(0,[z0,z1,z2,z3,z4,z6,z372]),(0,[z0,z1,z100,z2,z131,z4,z6]),(0,[z8,z0,z527,z1,z2,z3,z6]),(0,[z522,z0,z1,z2,z44,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z607]),(0,[z0,z1,z608,z2,z3,z4,z6])],[(0,[z1,z2,z42,z3,z49,z4,z6]),(0,[z0,z1,z609,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z24,z6,z33]),(0,[z0,z254,z1,z2,z13,z4,z6]),(0,[z0,z1,z2,z3,z591,z4,z6])],[(0,[z553,z0,z1,z2,z3,z4,z6]),(0,[z82,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z30,z2,z3,z38,z6])],[(0,[z610,z0,z1,z2,z3,z4,z6]),(0,[z611,z0,z1,z2,z3,z4,z6]),(0,[z251,z0,z2,z3,z13,z4,z6]),(1,[z0,z1,z2,z3,z223,z6]),(0,[z476,z0,z1,z2,z3,z309,z6])]],
   [[(0,[z0,z1,z2,z3,z16,z16,z6]),(1,[z29,z0,z1,z2,z6,z142])],[(0,[z21,z0,z1,z2,z227,z4,z6]),(0,[z0,z1,z2,z3,z4,z612,z6]),(0,[z29,z0,z1,z111,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z278,z6]),(0,[z29,z0,z1,z2,z4,z6,z142]),(0,[z0,z1,z46,z2,z44,z3,z6])],[(0,[z0,z1,z2,z3,z462,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z613]),(0,[z251,z0,z51,z2,z3,z4,z6]),(0,[z0,z2,z3,z244,z131,z4,z6]),(0,[z17,z0,z1,z2,z3,z317,z6])],[(0,[z8,z0,z1,z2,z3,z14,z6])],[(0,[z251,z0,z1,z2,z255,z4,z6]),(0,[z0,z1,z1,z2,z3,z16,z6]),(0,[z188,z0,z1,z2,z3,z4,z6]),(0,[z476,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z614,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z239]),(1,[z0,z1,z2,z3,z6,z146]),(0,[z263,z17,z0,z1,z2,z3,z6])],[(0,[z133,z184,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z615,z3,z4,z6]),(0,[z0,z254,z1,z2,z3,z14,z6]),(0,[z0,z1,z11,z2,z255,z3,z6]),(0,[z616,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z206,z37,z6]),(0,[z0,z1,z2,z3,z4,z617,z6]),(0,[z0,z1,z618,z2,z3,z4,z6])],[(0,[z0,z254,z1,z2,z3,z6,z33]),(0,[z17,z0,z1,z2,z3,z16,z6]),(0,[z197,z0,z1,z2,z3,z516,z6]),(0,[z0,z1,z2,z3,z619,z4,z6]),(0,[z0,z1,z2,z3,z309,z480,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z620,z6]),(0,[z184,z1,z190,z2,z3,z4,z6]),(0,[z0,z1,z2,z621,z3,z4,z6]),(0,[z0,z1,z51,z2,z3,z16,z6]),(1,[z28,z0,z2,z3,z16,z6]),(0,[z0,z1,z2,z622,z3,z4,z6]),(0,[z0,z126,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z4,z623,z6])],[(0,[z20,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z624,z2,z3,z4,z6]),(0,[z0,z40,z1,z2,z3,z4,z206]),(0,[z17,z0,z1,z2,z3,z131,z6]),(0,[z0,z1,z625,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z626,z6])],[(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z627,z6]),(0,[z0,z1,z628,z2,z3,z4,z6]),(0,[z0,z1,z2,z44,z3,z14,z6]),(1,[z29,z0,z1,z2,z3,z6])],[(0,[z0,z1,z629,z2,z3,z4,z6]),(0,[z0,z1,z630,z2,z3,z4,z6]),(0,[z25,z8,z0,z1,z2,z3,z6]),(0,[z251,z0,z1,z11,z2,z3,z6]),(0,[z0,z1,z2,z3,z16,z6,z560]),(0,[z0,z1,z2,z3,z14,z6,z136])],[(0,[z86,z80,z1,z2,z3,z4,z6]),(0,[z0,z1,z631,z2,z3,z4,z6]),(0,[z0,z254,z1,z2,z44,z3,z6]),(0,[z0,z1,z2,z3,z16,z309,z6]),(0,[z0,z1,z632,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z368])],[(0,[z633,z0,z1,z2,z3,z4,z6]),(0,[z23,z8,z0,z1,z2,z3,z6]),(0,[z82,z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z30,z170,z2,z4,z6]),(0,[z0,z1,z170,z3,z131,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z33]),(0,[z0,z458,z1,z2,z3,z4,z6])],[(0,[z17,z0,z1,z2,z3,z49,z6]),(0,[z0,z1,z2,z3,z4,z6,z634]),(0,[z0,z1,z2,z3,z14,z6,z103]),(0,[z0,z1,z2,z3,z4,z6,z448]),(0,[z29,z0,z159,z1,z2,z3,z6]),(0,[z635,z0,z1,z2,z3,z4,z6])],[(0,[z72,z1,z41,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z636,z6]),(0,[z0,z36,z1,z2,z3,z6,z33]),(1,[z0,z1,z2,z3,z367,z6]),(0,[z17,z0,z1,z63,z2,z3,z6]),(0,[z0,z637,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z207,z3,z4,z6]),(0,[z0,z638,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z14,z6,z107]),(0,[z0,z1,z639,z2,z3,z4,z6]),(0,[z29,z0,z1,z63,z2,z3,z6])],[(0,[z86,z0,z1,z11,z2,z3,z6]),(0,[z0,z1,z640,z2,z3,z4,z6]),(0,[z0,z51,z2,z255,z3,z4,z6]),(0,[z0,z1,z641,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z314,z4,z6]),(1,[z0,z1,z2,z3,z212,z6])],[(0,[z8,z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z11,z2,z3,z14,z6]),(1,[z0,z1,z378,z2,z3,z6])],[(0,[z184,z0,z1,z42,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z642,z6]),(0,[z21,z0,z1,z11,z2,z3,z6]),(0,[z82,z0,z2,z55,z3,z4,z6]),(0,[z643,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z255,z3,z13,z4,z6]),(0,[z0,z1,z2,z238,z255,z3,z6]),(0,[z17,z0,z1,z170,z2,z3,z6]),(0,[z0,z1,z644,z2,z3,z4,z6]),(0,[z0,z1,z602,z2,z3,z4,z6]),(0,[z17,z0,z1,z2,z3,z309,z6]),(0,[z17,z0,z1,z416,z2,z3,z6])],[(0,[z1,z190,z2,z42,z3,z4,z6]),(0,[z0,z36,z1,z2,z44,z3,z6]),(0,[z645,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z1,z2,z3,z131,z6]),(0,[z0,z1,z2,z524,z3,z4,z6]),(0,[z57,z29,z0,z1,z2,z3,z6]),(0,[z29,z0,z1,z2,z3,z309,z6]),(0,[z0,z1,z2,z646,z3,z4,z6])],[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z25,z0,z1,z53,z3,z4,z6]),(0,[z29,z0,z1,z51,z2,z3,z6]),(0,[z0,z254,z1,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z16,z206,z6]),(0,[z0,z1,z2,z3,z4,z647,z6]),(0,[z0,z1,z2,z3,z4,z480,z6])],[(1,[z0,z15,z1,z2,z3,z6]),(0,[z0,z1,z2,z648,z3,z4,z6]),(1,[z172,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z206,z6,z68]),(0,[z0,z1,z649,z2,z3,z4,z6]),(0,[z0,z1,z2,z303,z3,z4,z6]),(0,[z0,z1,z443,z2,z3,z4,z6])],[(0,[z0,z1,z2,z650,z3,z4,z6]),(0,[z0,z1,z2,z227,z3,z6,z33]),(0,[z28,z0,z1,z11,z2,z3,z6]),(0,[z0,z126,z1,z2,z3,z16,z6]),(0,[z0,z40,z1,z2,z3,z127,z6]),(0,[z8,z0,z1,z2,z3,z543,z6]),(0,[z0,z1,z2,z3,z6,z33,z136])]],
   [[(0,[z20,z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z651,z2,z3,z4,z6]),(0,[z0,z1,z652,z2,z3,z4,z6]),(0,[z17,z0,z1,z2,z3,z4,z6])],[(0,[z653,z0,z1,z2,z3,z4,z6]),(0,[z85,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z1,z2,z3,z49,z6]),(0,[z0,z1,z51,z2,z3,z4,z6]),(0,[z0,z1,z2,z44,z3,z16,z6]),(0,[z0,z1,z74,z11,z2,z3,z6])],[(0,[z80,z0,z1,z2,z3,z16,z6]),(0,[z654,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z655,z6]),(1,[z188,z0,z1,z2,z3,z6]),(0,[z8,z0,z1,z63,z2,z3,z6]),(0,[z0,z1,z2,z3,z249,z4,z6]),(0,[z0,z1,z2,z3,z6,z33,z103]),(0,[z0,z1,z48,z2,z3,z4,z309])],[(0,[z656,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z44,z3,z131,z6]),(0,[z0,z1,z657,z2,z3,z4,z6]),(0,[z0,z1,z46,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z221,z6])],[(0,[z0,z1,z658,z2,z3,z4,z6]),(0,[z0,z1,z2,z227,z44,z3,z6]),(0,[z17,z0,z1,z2,z3,z206,z6]),(0,[z0,z1,z2,z3,z6,z33,z107]),(0,[z0,z1,z2,z3,z4,z268,z6])],[(0,[z419,z29,z0,z1,z2,z3,z6]),(0,[z29,z0,z1,z2,z3,z6,z175])],[(0,[z82,z0,z1,z2,z3,z4,z6]),(0,[z82,z0,z1,z55,z3,z4,z6]),(0,[z0,z1,z659,z2,z3,z4,z6]),(0,[z8,z0,z1,z170,z2,z3,z6]),(0,[z8,z0,z1,z2,z3,z309,z6])],[(0,[z0,z1,z190,z3,z4,z6,z136])]],
   [[(1,[z151,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z44,z3,z49,z6]),(0,[z0,z1,z2,z3,z4,z660,z6]),(1,[z197,z0,z2,z3,z4,z68]),(0,[z8,z0,z379,z1,z2,z3,z6])],[(0,[z0,z1,z2,z661,z3,z4,z6]),(0,[z662,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z11,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z78,z14,z6]),(1,[z0,z1,z2,z3,z544,z6]),(0,[z0,z1,z135,z3,z4,z69,z6])],[(0,[z17,z80,z0,z1,z2,z3,z6]),(0,[z29,z0,z1,z41,z2,z3,z6]),(0,[z72,z0,z2,z3,z4,z6,z68]),(0,[z0,z1,z663,z2,z3,z4,z6]),(0,[z664,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z14,z81,z6]),(0,[z0,z1,z2,z3,z4,z665,z6]),(0,[z8,z0,z1,z2,z3,z666,z6]),(0,[z0,z1,z2,z667,z3,z4,z6]),(0,[z0,z1,z2,z3,z544,z6,z136]),(0,[z0,z1,z158,z2,z3,z4,z6]),(0,[z668,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z309,z6,z103]),(0,[z0,z669,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z670]),(0,[z0,z1,z2,z3,z4,z516,z6]),(0,[z0,z1,z11,z2,z3,z131,z6]),(0,[z8,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z671,z6]),(0,[z0,z1,z672,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z33,z185]),(0,[z0,z1,z628,z2,z55,z4,z6]),(0,[z0,z1,z54,z2,z3,z4,z6]),(1,[z0,z1,z2,z238,z3,z6]),(0,[z556,z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z4,z6,z673]),(0,[z0,z1,z109,z2,z3,z4,z6])],[(0,[z151,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z674,z6]),(0,[z0,z1,z2,z3,z49,z14,z6]),(0,[z0,z1,z675,z2,z3,z4,z6]),(0,[z676,z0,z1,z2,z3,z4,z6]),(0,[z28,z0,z126,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z666,z4,z6]),(0,[z0,z1,z2,z44,z3,z309,z6])],[(0,[z0,z1,z2,z3,z4,z6,z677]),(0,[z29,z0,z1,z2,z3,z24,z6]),(1,[z0,z1,z628,z2,z4,z6]),(0,[z0,z254,z1,z2,z3,z4,z6]),(1,[z0,z1,z79,z2,z3,z6])],[(0,[z0,z678,z1,z2,z3,z4,z6]),(0,[z0,z114,z1,z2,z3,z4,z6]),(0,[z0,z1,z100,z2,z3,z14,z6]),(0,[z8,z0,z1,z2,z3,z206,z6]),(0,[z0,z1,z2,z3,z679,z4,z6]),(0,[z0,z1,z63,z135,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z142]),(0,[z17,z0,z1,z169,z2,z3,z6])]],
   [[(0,[z0,z1,z11,z2,z3,z49,z6]),(0,[z0,z126,z1,z2,z3,z4,z6]),(0,[z0,z1,z100,z2,z3,z6,z33]),(0,[z0,z1,z680,z2,z3,z4,z6]),(0,[z29,z0,z1,z30,z2,z3,z6]),(0,[z0,z1,z63,z2,z3,z4,z136]),(0,[z0,z1,z2,z3,z4,z6,z681])],[(0,[z20,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z179,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z682]),(0,[z17,z0,z1,z100,z2,z3,z6])],[(0,[z17,z82,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z296,z55,z3,z6]),(0,[z683,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z684,z2,z3,z4,z6]),(0,[z0,z1,z2,z44,z3,z4,z6])],[(0,[z685,z0,z1,z2,z3,z4,z6]),(0,[z17,z21,z0,z1,z2,z3,z6]),(0,[z29,z82,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z686]),(0,[z0,z1,z2,z3,z417,z16,z6])],[(0,[z0,z687,z1,z2,z3,z4,z6]),(0,[z29,z21,z0,z1,z2,z3,z6]),(1,[z0,z1,z2,z3,z229,z6]),(0,[z0,z1,z111,z2,z4,z6,z103])],[(0,[z8,z80,z0,z1,z2,z3,z6]),(0,[z27,z0,z1,z2,z3,z81,z6]),(0,[z0,z1,z100,z2,z44,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z230]),(0,[z0,z1,z11,z2,z3,z309,z6])],[(0,[z0,z1,z2,z44,z3,z206,z6]),(0,[z0,z1,z39,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z287,z6]),(0,[z0,z1,z2,z3,z437,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z688]),(0,[z291,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z14,z4,z16,z6]),(0,[z117,z8,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z264]),(0,[z0,z1,z2,z44,z96,z4,z6]),(1,[z0,z1,z2,z3,z78,z33])]],
   [[(0,[z689,z0,z1,z2,z3,z4,z6]),(0,[z507,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z690,z3,z4,z6]),(0,[z0,z51,z2,z55,z3,z4,z6]),(0,[z29,z0,z1,z2,z255,z3,z6]),(0,[z0,z1,z2,z3,z78,z16,z6]),(0,[z148,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z4,z206,z6]),(1,[z0,z1,z2,z3,z591,z6]),(0,[z0,z691,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z692,z3,z4,z6]),(0,[z0,z1,z2,z9,z3,z4,z6]),(1,[z8,z0,z1,z3,z6,z107]),(0,[z160,z29,z0,z1,z2,z3,z6])],[(0,[z693,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z53,z2,z3,z4,z6]),(0,[z694,z0,z1,z2,z3,z4,z6]),(0,[z0,z36,z51,z2,z3,z4,z6]),(0,[z0,z1,z11,z2,z3,z4,z6]),(0,[z8,z0,z1,z169,z2,z3,z6])],[(0,[z29,z20,z0,z1,z2,z3,z6]),(0,[z23,z94,z1,z2,z3,z4,z6]),(0,[z0,z1,z510,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z695,z4,z6]),(0,[z29,z251,z0,z1,z2,z3,z6]),(0,[z0,z254,z1,z11,z2,z3,z6]),(1,[z0,z1,z2,z3,z269,z6]),(0,[z156,z0,z1,z2,z3,z6,z33])],[(0,[z0,z1,z2,z3,z696,z4,z6]),(0,[z0,z1,z2,z3,z49,z16,z6]),(0,[z8,z0,z1,z100,z2,z3,z6]),(1,[z8,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z697,z4,z6]),(0,[z17,z0,z1,z443,z2,z3,z6])],[(0,[z0,z1,z2,z3,z698,z4,z6]),(0,[z0,z1,z2,z3,z87,z6,z33]),(0,[z0,z1,z2,z3,z699,z4,z6]),(0,[z8,z82,z0,z1,z2,z3,z6]),(1,[z251,z0,z2,z13,z4,z6]),(0,[z0,z1,z2,z3,z4,z700,z6]),(0,[z556,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z16,z6,z33]),(0,[z414,z0,z1,z2,z3,z4,z6])],[(0,[z701,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z227,z3,z4,z6]),(0,[z8,z21,z0,z1,z2,z3,z6]),(0,[z702,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z100,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z18,z14,z6]),(0,[z0,z703,z1,z2,z3,z4,z6]),(0,[z0,z1,z11,z2,z3,z206,z6]),(0,[z0,z1,z174,z2,z3,z4,z6])],[(0,[z553,z0,z1,z2,z3,z49,z6]),(0,[z704,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z705]),(1,[z0,z1,z2,z3,z340,z6]),(0,[z418,z0,z1,z2,z3,z4,z6]),(1,[z0,z2,z3,z14,z16,z6]),(0,[z0,z1,z2,z3,z18,z6,z33]),(0,[z336,z0,z1,z2,z3,z4,z6]),(0,[z706,z0,z1,z2,z3,z4,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z707,z0,z1,z2,z3,z6]),(0,[z453,z0,z2,z3,z4,z68]),(0,[z0,z1,z2,z708,z3,z6]),(0,[z0,z1,z2,z3,z709,z6]),(0,[z0,z710,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z711,z6]),(0,[z164,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z712,z6]),(0,[z8,z0,z1,z3,z6,z167]),(0,[z0,z1,z46,z74,z3,z6]),(0,[z0,z1,z79,z2,z44,z6])],[(0,[z0,z1,z2,z713,z3,z6]),(0,[z0,z443,z2,z3,z6,z68]),(0,[z0,z714,z2,z3,z4,z6]),(0,[z0,z1,z2,z44,z626,z6]),(0,[z0,z1,z378,z2,z3,z6])],[(0,[z82,z0,z55,z3,z4,z6]),(0,[z0,z1,z2,z3,z715,z6]),(0,[z0,z1,z716,z2,z3,z6]),(0,[z1,z717,z2,z3,z4,z6]),(0,[z57,z1,z298,z2,z3,z6]),(0,[z718,z0,z2,z3,z4,z6]),(0,[z8,z719,z1,z2,z3,z6]),(0,[z0,z1,z63,z2,z3,z230])],[(0,[z0,z720,z1,z2,z3,z6]),(0,[z0,z15,z1,z2,z3,z68]),(0,[z0,z1,z2,z3,z166,z198]),(0,[z405,z0,z2,z3,z244,z6]),(0,[z0,z1,z2,z3,z721,z6]),(0,[z722,z0,z1,z2,z3,z6]),(0,[z419,z0,z1,z2,z3,z175])],[(0,[z173,z1,z2,z3,z4,z6]),(0,[z0,z1,z723,z2,z3,z6]),(0,[z0,z36,z1,z628,z4,z6]),(0,[z0,z1,z628,z2,z16,z6]),(0,[z724,z0,z1,z2,z3,z6]),(0,[z0,z1,z725,z2,z3,z6]),(0,[z0,z1,z2,z3,z726,z6]),(0,[z0,z1,z2,z3,z727,z6])],[(0,[z172,z1,z2,z3,z4,z6]),(0,[z17,z0,z114,z2,z3,z6]),(0,[z0,z1,z2,z3,z728,z6]),(0,[z251,z0,z2,z13,z6,z33]),(0,[z0,z729,z1,z2,z3,z6]),(0,[z0,z15,z1,z2,z3,z6]),(0,[z0,z2,z3,z244,z16,z6]),(0,[z0,z1,z2,z3,z730,z6]),(0,[z0,z1,z731,z2,z3,z6])],[(0,[z0,z1,z218,z26,z4,z6]),(0,[z0,z1,z2,z3,z732,z6]),(0,[z0,z1,z733,z2,z3,z6]),(0,[z17,z82,z0,z55,z3,z6]),(0,[z82,z0,z377,z2,z3,z6]),(0,[z0,z1,z2,z3,z734,z6]),(0,[z197,z0,z2,z3,z516,z68]),(0,[z0,z1,z2,z3,z309,z230]),(0,[z29,z0,z1,z63,z3,z136])],[(0,[z0,z1,z2,z3,z735,z6]),(0,[z17,z0,z1,z53,z3,z6]),(0,[z736,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z737,z3,z6]),(0,[z0,z1,z2,z3,z738,z6]),(0,[z0,z1,z2,z3,z6,z739]),(0,[z85,z1,z2,z3,z45,z6])]],
   [[(0,[z0,z1,z2,z3,z6,z740]),(0,[z0,z510,z53,z3,z4,z6]),(0,[z25,z510,z2,z3,z4,z185]),(0,[z0,z1,z2,z741,z3,z6]),(0,[z0,z1,z742,z2,z3,z6]),(0,[z0,z1,z2,z3,z743,z6]),(0,[z0,z1,z2,z744,z3,z6]),(0,[z745,z0,z1,z2,z3,z6]),(0,[z0,z1,z111,z2,z269,z103]),(0,[z263,z0,z1,z2,z317,z6])],[(0,[z0,z1,z746,z3,z4,z6]),(0,[z747,z0,z1,z2,z3,z6])],[(0,[z748,z0,z1,z2,z3,z6]),(0,[z0,z2,z3,z4,z6,z749]),(0,[z94,z1,z2,z3,z577,z6]),(0,[z750,z0,z1,z2,z3,z6]),(0,[z0,z1,z751,z2,z3,z6]),(0,[z0,z1,z752,z2,z3,z6])],[(0,[z753,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z754,z6]),(0,[z0,z1,z755,z2,z3,z4]),(0,[z0,z463,z2,z3,z14,z6]),(0,[z29,z0,z1,z2,z473,z6]),(0,[z0,z114,z2,z179,z4,z6]),(0,[z756,z0,z1,z2,z3,z6]),(0,[z0,z2,z3,z757,z16,z6]),(0,[z0,z1,z758,z2,z3,z6]),(0,[z0,z1,z3,z4,z759,z136])],[(0,[z0,z1,z2,z760,z4,z6]),(0,[z0,z1,z2,z3,z761,z6]),(0,[z1,z2,z3,z4,z6,z762]),(0,[z0,z1,z763,z3,z6,z198]),(0,[z764,z0,z1,z2,z3,z6]),(0,[z0,z1,z765,z131,z4,z6]),(0,[z766,z0,z1,z2,z3,z6]),(0,[z0,z1,z111,z2,z4,z767])],[(0,[z0,z1,z2,z3,z768,z6]),(0,[z0,z1,z769,z2,z3,z4]),(0,[z0,z1,z770,z2,z3,z6]),(0,[z20,z1,z2,z49,z16,z6]),(0,[z0,z1,z2,z3,z771,z6]),(0,[z8,z0,z114,z2,z3,z6]),(0,[z0,z1,z772,z2,z3,z6]),(0,[z29,z0,z1,z111,z2,z103]),(0,[z0,z1,z111,z2,z12,z103])],[(0,[z0,z1,z773,z2,z3,z6]),(0,[z0,z1,z2,z3,z774,z6]),(1,[z0,z1,z763,z3,z6]),(0,[z0,z1,z775,z2,z3,z6]),(0,[z776,z0,z1,z2,z3,z6]),(0,[z0,z1,z777,z2,z3,z6])],[(0,[z151,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z778,z6]),(0,[z0,z1,z2,z179,z14,z6]),(0,[z0,z1,z170,z395,z4,z6]),(0,[z65,z0,z1,z628,z2,z6]),(0,[z0,z1,z2,z3,z779,z6]),(0,[z8,z0,z1,z323,z3,z6]),(0,[z1,z780,z2,z3,z4,z6]),(0,[z8,z0,z1,z509,z3,z6])]],
   [[(0,[z0,z1,z781,z3,z4,z6]),(0,[z0,z1,z2,z782,z3,z6]),(0,[z0,z1,z54,z2,z14,z6]),(0,[z468,z0,z1,z170,z2,z6]),(0,[z0,z1,z763,z2,z3,z6]),(0,[z0,z1,z783,z2,z3,z6]),(0,[z197,z172,z2,z3,z4,z68]),(0,[z0,z1,z2,z3,z784,z6])],[(0,[z0,z785,z2,z3,z4,z6]),(0,[z786,z0,z1,z2,z3,z6]),(0,[z0,z1,z54,z2,z6,z33]),(0,[z1,z787,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z204,z6]),(0,[z210,z1,z2,z3,z87,z6]),(0,[z0,z1,z788,z2,z3,z6]),(0,[z0,z1,z2,z789,z3,z6]),(0,[z0,z1,z2,z3,z790,z6]),(0,[z0,z1,z2,z3,z6,z791]),(0,[z0,z1,z2,z3,z6,z198]),(0,[z57,z0,z1,z174,z3,z6]),(0,[z792,z1,z2,z3,z4,z6]),(0,[z360,z0,z170,z131,z4,z6]),(0,[z418,z0,z158,z2,z3,z6])],[(0,[z0,z1,z2,z3,z793,z6]),(0,[z0,z1,z2,z794,z4,z6]),(0,[z151,z133,z1,z42,z3,z6]),(0,[z0,z1,z2,z3,z795,z6]),(0,[z0,z337,z1,z2,z3,z33]),(0,[z0,z1,z2,z238,z3,z6]),(0,[z0,z2,z3,z796,z4,z6]),(0,[z0,z1,z2,z3,z6,z797]),(0,[z0,z1,z2,z3,z33,z171]),(0,[z0,z1,z2,z3,z798,z6])],[(0,[z0,z1,z2,z3,z233,z6]),(0,[z556,z0,z1,z51,z3,z6]),(0,[z117,z0,z377,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z163]),(0,[z799,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z800,z6]),(0,[z0,z1,z39,z2,z44,z6])],[(0,[z29,z0,z1,z2,z690,z6]),(0,[z0,z510,z2,z3,z801,z6]),(0,[z0,z1,z628,z2,z4,z6]),(0,[z0,z1,z2,z3,z6,z802]),(0,[z251,z0,z2,z13,z498,z6]),(0,[z0,z1,z803,z3,z4,z6]),(0,[z0,z15,z1,z2,z3,z198]),(0,[z188,z0,z1,z450,z3,z6])],[(0,[z0,z114,z218,z3,z4,z6]),(0,[z0,z1,z2,z44,z179,z6]),(0,[z0,z1,z2,z3,z6,z804]),(0,[z0,z2,z3,z244,z4,z6]),(0,[z17,z197,z0,z2,z3,z68]),(0,[z0,z1,z2,z3,z6,z805]),(0,[z0,z1,z39,z74,z2,z6]),(0,[z806,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z807,z6]),(0,[z0,z1,z2,z3,z808,z6]),(0,[z0,z1,z2,z3,z809,z6]),(0,[z0,z1,z2,z3,z810,z6]),(0,[z0,z811,z1,z2,z3,z6]),(0,[z360,z0,z2,z3,z223,z6]),(0,[z0,z1,z2,z3,z812,z6]),(0,[z0,z1,z813,z2,z3,z6]),(0,[z0,z1,z814,z2,z3,z6]),(0,[z0,z1,z2,z3,z815,z6])]],
   [[(0,[z0,z1,z816,z3,z4,z6]),(0,[z468,z0,z1,z2,z49,z6]),(0,[z0,z1,z2,z3,z817,z6]),(0,[z474,z1,z2,z3,z67,z6]),(0,[z0,z1,z2,z3,z818,z6])],[(0,[z0,z1,z2,z819,z3,z6]),(0,[z0,z820,z2,z3,z4,z6]),(0,[z20,z1,z2,z821,z4,z6]),(0,[z0,z1,z2,z3,z822,z6])],[(0,[z0,z1,z218,z3,z14,z6]),(0,[z360,z0,z170,z3,z4,z6])],[(0,[z17,z0,z1,z2,z3,z6]),(0,[z823,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z824,z6]),(0,[z825,z0,z1,z2,z3,z6]),(0,[z0,z826,z1,z2,z3,z6]),(0,[z1,z2,z3,z14,z6,z248])],[(0,[z0,z1,z196,z3,z229,z6]),(0,[z827,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z828]),(0,[z468,z0,z1,z2,z6,z560]),(0,[z197,z0,z11,z2,z3,z68]),(0,[z0,z2,z3,z4,z6,z829]),(0,[z0,z1,z2,z3,z6,z830]),(0,[z420,z1,z2,z3,z6,z239])],[(0,[z0,z1,z2,z3,z6,z831]),(0,[z0,z1,z2,z3,z832,z6]),(0,[z468,z0,z1,z2,z6,z142]),(0,[z57,z0,z1,z2,z9,z6])],[(0,[z0,z1,z2,z4,z833,z6]),(0,[z20,z1,z2,z49,z4,z6]),(0,[z0,z1,z53,z3,z104,z6]),(0,[z0,z1,z2,z179,z16,z6]),(0,[z0,z196,z255,z3,z4,z6]),(0,[z0,z1,z2,z834,z3,z6]),(0,[z8,z197,z0,z2,z3,z68]),(0,[z0,z1,z2,z3,z835,z6]),(0,[z0,z1,z2,z3,z78,z33])],[(0,[z0,z1,z2,z3,z836,z6]),(0,[z0,z837,z2,z3,z4,z6]),(0,[z838,z0,z1,z2,z3,z6]),(0,[z0,z1,z54,z2,z16,z6]),(0,[z65,z0,z1,z54,z2,z6]),(0,[z29,z0,z1,z196,z3,z6]),(0,[z149,z0,z443,z2,z3,z6]),(0,[z0,z1,z2,z3,z839,z6]),(0,[z0,z1,z2,z3,z6,z840])]],
   [[(0,[z0,z1,z2,z3,z841,z6]),(0,[z0,z1,z2,z3,z842,z6]),(0,[z251,z0,z2,z44,z13,z6]),(0,[z0,z2,z3,z14,z647,z6])],[(0,[z82,z0,z569,z3,z4,z6]),(0,[z843,z0,z1,z628,z2,z6]),(0,[z0,z1,z2,z3,z844,z6]),(0,[z0,z1,z845,z2,z3,z6]),(0,[z0,z1,z2,z3,z846,z6]),(0,[z0,z1,z2,z3,z6,z847]),(0,[z0,z1,z2,z3,z6,z848]),(0,[z8,z0,z1,z2,z3,z849]),(0,[z0,z1,z850,z2,z3,z6])],[(0,[z851,z0,z1,z2,z3,z6]),(0,[z852,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z853,z6]),(0,[z0,z1,z2,z3,z6,z854]),(0,[z0,z1,z2,z3,z855,z6]),(0,[z0,z11,z2,z3,z244,z6]),(0,[z0,z1,z2,z3,z6,z856]),(0,[z0,z1,z2,z3,z269,z6])],[(0,[z8,z0,z1,z2,z3,z6]),(0,[z1,z2,z3,z857,z24,z6]),(0,[z172,z510,z2,z3,z4,z6]),(0,[z0,z1,z858,z2,z3,z6])],[(0,[z0,z1,z2,z3,z859,z6]),(0,[z17,z20,z1,z2,z49,z6]),(0,[z0,z1,z860,z3,z4,z6]),(0,[z0,z1,z2,z861,z3,z6]),(0,[z82,z0,z11,z55,z3,z6]),(0,[z0,z1,z862,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z863]),(0,[z0,z1,z2,z3,z864,z6]),(0,[z8,z251,z0,z2,z13,z6]),(0,[z0,z1,z3,z4,z6,z865]),(0,[z0,z158,z2,z255,z3,z6]),(0,[z0,z1,z866,z2,z3,z6]),(0,[z28,z0,z443,z2,z3,z6]),(0,[z867,z0,z1,z2,z3,z6])],[(0,[z0,z1,z868,z2,z3,z6]),(0,[z124,z1,z2,z3,z81,z33]),(0,[z0,z1,z628,z11,z2,z6]),(0,[z251,z0,z196,z13,z4,z6]),(0,[z29,z0,z1,z297,z3,z6]),(0,[z0,z2,z3,z16,z6,z343]),(0,[z0,z1,z2,z3,z230,z103]),(0,[z301,z1,z2,z524,z3,z6]),(0,[z0,z1,z111,z2,z44,z103]),(0,[z0,z1,z869,z2,z6,z33])],[(0,[z72,z510,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z870,z6]),(0,[z0,z1,z2,z871,z4,z6]),(0,[z0,z1,z218,z179,z4,z6]),(0,[z0,z1,z2,z3,z340,z6]),(0,[z0,z1,z51,z234,z3,z6]),(0,[z0,z1,z2,z3,z872,z6]),(0,[z0,z1,z873,z2,z3,z6]),(0,[z0,z1,z2,z300,z3,z6]),(0,[z0,z1,z2,z300,z6,z103])],[(0,[z8,z133,z1,z42,z3,z6]),(0,[z310,z1,z2,z3,z87,z6]),(0,[z0,z1,z2,z3,z874,z6]),(0,[z1,z2,z3,z6,z33,z248]),(0,[z29,z0,z1,z2,z44,z6])]],
   [[(0,[z0,z1,z2,z3,z875,z6]),(0,[z251,z0,z2,z395,z4,z6]),(0,[z0,z1,z876,z2,z3,z6]),(0,[z1,z2,z3,z6,z877,z198]),(0,[z0,z1,z2,z3,z14,z878]),(0,[z173,z1,z2,z3,z6,z33]),(0,[z17,z0,z1,z63,z3,z136]),(0,[z0,z1,z2,z3,z279,z6])],[(0,[z0,z1,z2,z879,z3,z6]),(0,[z556,z0,z1,z42,z3,z6]),(0,[z0,z880,z2,z3,z4,z6]),(0,[z27,z0,z1,z2,z3,z6]),(0,[z94,z1,z2,z3,z6,z368]),(0,[z0,z1,z218,z3,z16,z6]),(0,[z0,z2,z3,z4,z757,z6]),(0,[z0,z1,z2,z3,z6,z881]),(0,[z0,z1,z2,z3,z882,z6]),(0,[z0,z1,z2,z3,z883,z6]),(0,[z0,z1,z2,z3,z884,z6])],[(0,[z0,z1,z2,z3,z885,z6]),(0,[z0,z886,z2,z3,z4,z6]),(0,[z251,z0,z2,z796,z4,z6]),(0,[z0,z1,z887,z2,z3,z6]),(0,[z0,z1,z2,z3,z38,z6]),(0,[z188,z0,z1,z416,z3,z6]),(0,[z0,z1,z2,z3,z888,z6])],[(0,[z0,z1,z2,z889,z4,z6]),(0,[z890,z0,z1,z2,z3,z6]),(0,[z0,z2,z3,z14,z660,z6]),(0,[z0,z1,z2,z3,z4,z891]),(0,[z82,z0,z892,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z893]),(0,[z0,z1,z46,z2,z3,z6])],[(0,[z0,z1,z2,z894,z3,z6]),(0,[z895,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z896,z6]),(0,[z897,z1,z2,z3,z4,z6]),(0,[z0,z503,z2,z3,z16,z6]),(0,[z0,z1,z898,z2,z3,z6]),(0,[z0,z1,z2,z899,z3,z6])],[(0,[z0,z1,z2,z3,z900,z6]),(0,[z901,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z252,z33]),(0,[z17,z0,z1,z2,z3,z163]),(0,[z173,z1,z2,z44,z3,z6]),(0,[z0,z1,z2,z3,z902,z6]),(0,[z0,z1,z2,z3,z903,z6]),(0,[z0,z1,z111,z2,z3,z175])],[(0,[z0,z114,z2,z26,z4,z6]),(0,[z0,z1,z2,z3,z904,z6]),(0,[z0,z1,z2,z3,z163,z68]),(0,[z0,z1,z2,z3,z905,z6])],[(0,[z86,z0,z443,z2,z3,z6]),(0,[z0,z1,z2,z179,z4,z6]),(0,[z0,z1,z2,z3,z312,z33]),(0,[z29,z173,z1,z2,z3,z6]),(0,[z8,z0,z1,z450,z3,z6]),(0,[z17,z0,z1,z111,z2,z103])]],
   [[(0,[z25,z29,z1,z2,z3,z185]),(0,[z82,z0,z55,z3,z125,z6]),(0,[z0,z1,z54,z2,z4,z6]),(0,[z0,z1,z2,z3,z906,z6]),(0,[z0,z1,z3,z4,z907,z6]),(0,[z17,z0,z1,z2,z3,z243]),(0,[z8,z0,z1,z63,z3,z136]),(0,[z0,z1,z2,z3,z287,z33]),(0,[z0,z1,z3,z4,z6,z759]),(0,[z908,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z909,z6]),(0,[z0,z1,z910,z2,z3,z6])],[(0,[z0,z1,z2,z3,z246,z6]),(0,[z0,z2,z3,z911,z4,z6]),(0,[z0,z912,z1,z2,z3,z6]),(0,[z0,z1,z2,z913,z3,z6]),(0,[z0,z1,z2,z3,z914,z6])],[(0,[z20,z1,z2,z44,z49,z6]),(0,[z0,z1,z2,z26,z14,z6]),(0,[z0,z1,z2,z3,z322,z6]),(0,[z0,z1,z915,z2,z3,z6]),(0,[z29,z0,z1,z2,z6,z739]),(0,[z916,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z917,z6]),(0,[z29,z0,z1,z2,z189,z6]),(0,[z0,z1,z2,z3,z918,z6]),(0,[z0,z1,z2,z3,z919,z6]),(0,[z0,z920,z2,z3,z4,z6]),(0,[z0,z1,z921,z3,z4,z6]),(0,[z29,z0,z510,z2,z3,z6]),(0,[z0,z1,z2,z26,z6,z33]),(0,[z25,z1,z2,z3,z33,z185]),(0,[z0,z1,z869,z2,z16,z6]),(0,[z0,z1,z3,z4,z922,z6]),(0,[z0,z1,z2,z3,z923,z6]),(0,[z0,z924,z170,z2,z3,z6]),(0,[z0,z1,z46,z170,z3,z6]),(0,[z0,z1,z2,z3,z925,z6])],[(0,[z0,z1,z2,z3,z926,z6]),(0,[z17,z0,z1,z579,z2,z3]),(0,[z0,z1,z2,z3,z927,z6]),(0,[z0,z1,z2,z3,z928,z6])],[(0,[z124,z0,z1,z2,z3,z163]),(0,[z82,z0,z1,z400,z3,z6]),(0,[z0,z1,z2,z929,z3,z6]),(0,[z0,z1,z2,z3,z334,z6]),(0,[z0,z1,z2,z3,z930,z6]),(0,[z0,z1,z2,z3,z931,z6]),(0,[z0,z1,z79,z2,z6,z34])],[(0,[z0,z1,z2,z3,z73,z6]),(0,[z0,z1,z932,z2,z3,z6]),(0,[z0,z1,z2,z44,z26,z6]),(0,[z933,z1,z2,z3,z4,z6]),(0,[z349,z1,z2,z3,z577,z6]),(0,[z934,z0,z1,z2,z3,z6]),(0,[z0,z2,z3,z4,z893,z68]),(0,[z0,z236,z147,z2,z3,z6])],[(0,[z0,z1,z2,z3,z935,z6]),(0,[z0,z1,z2,z936,z3,z6]),(0,[z0,z1,z234,z55,z3,z6]),(0,[z0,z1,z2,z937,z3,z6]),(0,[z8,z0,z1,z111,z2,z103])]],
   [[(0,[z0,z1,z2,z3,z938,z6]),(0,[z0,z1,z2,z3,z939,z6]),(0,[z0,z1,z2,z3,z66,z6]),(0,[z0,z1,z940,z628,z2,z6]),(0,[z0,z1,z297,z3,z229,z6]),(0,[z941,z0,z1,z2,z3,z6]),(0,[z0,z924,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z942,z6])],[(0,[z943,z0,z1,z2,z3,z6]),(0,[z447,z1,z2,z3,z24,z6]),(0,[z0,z1,z2,z3,z944,z6]),(0,[z0,z1,z945,z2,z3,z6]),(0,[z946,z0,z1,z2,z3,z6]),(0,[z947,z0,z1,z2,z3,z6]),(0,[z57,z0,z1,z170,z131,z6]),(0,[z0,z948,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z175,z136]),(0,[z0,z1,z2,z949,z3,z6])],[(0,[z0,z1,z2,z3,z950,z6]),(0,[z0,z1,z2,z3,z951,z6]),(0,[z0,z1,z218,z3,z4,z6]),(0,[z0,z1,z2,z3,z952,z6]),(0,[z0,z1,z2,z3,z953,z6]),(0,[z0,z1,z2,z3,z6,z954]),(0,[z0,z955,z1,z2,z3,z6]),(0,[z57,z0,z924,z2,z3,z6]),(0,[z956,z1,z74,z2,z3,z6]),(0,[z0,z2,z3,z244,z6,z33]),(0,[z0,z1,z2,z3,z6,z957]),(0,[z8,z0,z1,z3,z6,z356])],[(0,[z0,z1,z2,z958,z4,z6]),(0,[z0,z1,z3,z4,z959,z6]),(0,[z65,z82,z0,z55,z3,z6]),(0,[z0,z1,z2,z3,z960,z6]),(0,[z251,z0,z1,z196,z4,z6]),(0,[z0,z1,z961,z3,z4,z6]),(0,[z0,z1,z2,z3,z127,z6]),(0,[z0,z1,z256,z11,z3,z6]),(0,[z0,z1,z2,z3,z962,z6]),(0,[z0,z1,z2,z3,z6,z963]),(0,[z57,z799,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z964,z6]),(0,[z965,z0,z1,z2,z3,z6]),(0,[z263,z0,z1,z2,z300,z6]),(0,[z0,z1,z2,z3,z306,z33])],[(0,[z17,z0,z1,z2,z3,z492]),(0,[z0,z1,z2,z3,z966,z6]),(0,[z0,z1,z2,z967,z3,z6]),(0,[z0,z1,z2,z3,z6,z968]),(0,[z0,z1,z2,z3,z969,z6]),(0,[z29,z360,z0,z2,z3,z6]),(0,[z0,z970,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z971,z6]),(0,[z0,z1,z2,z3,z6,z972])],[(0,[z0,z1,z2,z973,z3,z6]),(0,[z0,z1,z2,z44,z195,z6]),(0,[z0,z1,z11,z2,z179,z6]),(0,[z974,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z975]),(0,[z29,z251,z0,z2,z13,z6]),(0,[z0,z1,z2,z3,z6,z976]),(0,[z977,z0,z1,z2,z3,z6]),(0,[z29,z172,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z978,z6]),(0,[z0,z1,z2,z3,z979,z6]),(0,[z0,z1,z2,z3,z980,z6]),(0,[z0,z1,z53,z3,z50,z6]),(0,[z0,z1,z2,z4,z981,z6]),(0,[z0,z982,z1,z2,z3,z6]),(0,[z983,z1,z2,z3,z6,z198]),(0,[z0,z1,z2,z3,z78,z230]),(0,[z984,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z985,z6])],[(0,[z0,z1,z986,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z987]),(0,[z988,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z989,z6]),(0,[z0,z1,z2,z3,z990,z6]),(0,[z57,z0,z1,z2,z666,z6]),(0,[z0,z1,z2,z3,z6,z991]),(0,[z88,z0,z443,z2,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z992,z6]),(0,[z0,z1,z2,z3,z993,z6]),(0,[z994,z0,z1,z2,z3,z6]),(0,[z0,z1,z54,z11,z2,z6]),(0,[z0,z1,z995,z2,z3,z6]),(0,[z996,z0,z1,z2,z3,z6]),(0,[z1,z74,z997,z2,z3,z6]),(0,[z8,z0,z1,z3,z6,z374]),(0,[z0,z1,z2,z3,z998,z6])],[(0,[z8,z0,z1,z3,z6,z376]),(0,[z0,z1,z2,z26,z16,z6]),(0,[z251,z0,z297,z13,z4,z6]),(0,[z8,z0,z999,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1000,z6]),(0,[z20,z1,z2,z49,z6,z33]),(0,[z0,z114,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z1001,z6]),(0,[z0,z1,z1002,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1003]),(0,[z0,z1,z135,z416,z3,z6]),(0,[z0,z1,z1004,z2,z3,z6])],[(0,[z0,z114,z2,z3,z6,z33]),(0,[z0,z1,z2,z26,z104,z6]),(0,[z1005,z0,z1,z2,z3,z6]),(0,[z556,z0,z1,z30,z3,z6]),(0,[z1,z2,z3,z4,z6,z877]),(0,[z0,z1,z2,z3,z75,z33]),(0,[z0,z1,z2,z1006,z3,z6])],[(0,[z0,z1,z2,z821,z4,z6]),(0,[z0,z1,z2,z3,z1007,z6]),(0,[z1008,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1009,z6]),(0,[z0,z1,z2,z1010,z4,z6]),(0,[z0,z1,z869,z2,z4,z6])],[(0,[z1011,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1012,z6]),(0,[z0,z1,z2,z3,z1013,z6]),(0,[z0,z1,z2,z3,z6,z1014]),(0,[z0,z1,z3,z922,z6,z198]),(0,[z405,z0,z1,z170,z131,z6]),(0,[z0,z1,z2,z3,z69,z175])],[(0,[z1015,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1016]),(0,[z82,z0,z649,z3,z4,z6]),(0,[z0,z1,z2,z3,z1017,z6]),(0,[z0,z1,z2,z3,z1018,z6]),(0,[z168,z0,z1,z2,z6,z372]),(0,[z0,z1,z2,z1019,z3,z6]),(0,[z0,z1,z1020,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z171]),(0,[z0,z1,z1021,z2,z3,z6])],[(0,[z1022,z0,z1,z2,z3,z6]),(0,[z0,z1,z1023,z2,z3,z6]),(0,[z0,z1,z2,z3,z1024,z6]),(0,[z0,z1,z2,z3,z1025,z6]),(0,[z0,z1,z377,z2,z3,z6]),(0,[z251,z0,z11,z2,z13,z6]),(0,[z17,z0,z1,z297,z3,z6]),(0,[z0,z1,z1026,z2,z3,z6]),(0,[z0,z1,z1027,z2,z3,z6]),(0,[z0,z40,z2,z3,z16,z206]),(0,[z0,z1,z2,z3,z1028,z6]),(0,[z0,z1,z2,z3,z6,z175]),(0,[z0,z1,z1029,z2,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z878]),(0,[z94,z1,z2,z3,z857,z6]),(0,[z0,z114,z2,z44,z3,z6]),(0,[z1030,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z177,z6]),(0,[z0,z1,z2,z44,z152,z6]),(0,[z0,z338,z2,z238,z3,z6])],[(0,[z0,z1,z2,z3,z4,z1031]),(0,[z133,z1,z42,z3,z14,z6]),(0,[z133,z1,z207,z42,z3,z6]),(0,[z414,z1,z2,z3,z87,z6]),(0,[z0,z1,z2,z3,z1032,z6]),(0,[z0,z1,z2,z3,z1033,z6]),(0,[z8,z0,z1,z196,z3,z6]),(0,[z0,z1,z1034,z2,z3,z6]),(0,[z0,z1,z39,z170,z2,z6]),(0,[z0,z2,z3,z4,z1035,z6]),(0,[z0,z1,z109,z2,z3,z6]),(0,[z0,z1,z109,z2,z3,z287]),(0,[z29,z0,z1,z2,z6,z483])],[(0,[z0,z1,z2,z3,z108,z33]),(0,[z0,z1,z1036,z2,z3,z6])],[(0,[z1037,z0,z1,z2,z3,z6]),(0,[z21,z1,z2,z227,z44,z6]),(0,[z1038,z0,z1,z2,z3,z6]),(0,[z82,z0,z2,z303,z3,z6]),(0,[z1039,z0,z1,z2,z3,z6]),(1,[z0,z1,z2,z3,z1040]),(0,[z0,z1,z2,z3,z1041,z6])],[(0,[z0,z1,z2,z1042,z3,z6]),(0,[z0,z1,z1043,z3,z4,z6]),(0,[z1044,z0,z1,z2,z3,z6]),(0,[z0,z1,z111,z2,z14,z103]),(0,[z0,z1,z2,z1045,z3,z6]),(0,[z0,z1,z2,z3,z1046,z6])],[(0,[z1047,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1048,z6]),(0,[z0,z1,z2,z3,z1049,z6]),(0,[z251,z0,z1,z79,z2,z6]),(0,[z0,z1,z297,z3,z906,z6]),(0,[z29,z0,z1,z2,z505,z6]),(0,[z0,z1,z2,z1050,z3,z6]),(0,[z0,z1,z1051,z2,z3,z6]),(0,[z8,z0,z1,z11,z3,z6])],[(0,[z25,z1,z53,z3,z4,z185]),(0,[z0,z1,z1052,z3,z4,z6]),(0,[z251,z0,z196,z3,z4,z6]),(0,[z0,z1053,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1054,z6]),(0,[z0,z1,z170,z174,z3,z6]),(0,[z1055,z0,z1,z2,z3,z6]),(0,[z0,z1,z1056,z2,z3,z6]),(0,[z0,z1,z400,z135,z3,z6]),(0,[z0,z1,z2,z3,z1057,z6])],[(0,[z1058,z80,z2,z3,z4,z6]),(0,[z0,z1,z2,z1059,z3,z6]),(0,[z0,z1,z1060,z218,z3,z6]),(0,[z0,z1,z2,z1061,z3,z6]),(0,[z8,z0,z1,z297,z3,z6]),(0,[z0,z1,z2,z3,z1062,z6]),(0,[z8,z0,z2,z3,z244,z6]),(0,[z29,z0,z1,z2,z469,z6]),(0,[z0,z1,z2,z1063,z3,z6])]],
   [[(0,[z0,z1,z2,z207,z3,z6]),(0,[z0,z1,z2,z3,z1064,z6]),(0,[z0,z1,z2,z3,z1065,z6]),(0,[z299,z0,z1,z2,z3,z230]),(0,[z17,z1066,z1,z2,z3,z6])],[(0,[z0,z1,z1067,z3,z4,z6]),(0,[z0,z1,z39,z2,z49,z6]),(0,[z0,z114,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z6,z1068]),(0,[z82,z0,z55,z3,z5,z6]),(0,[z0,z36,z158,z2,z3,z6]),(0,[z0,z147,z2,z303,z3,z6]),(0,[z1069,z1,z2,z3,z4,z6]),(0,[z0,z1,z1070,z2,z3,z6]),(0,[z149,z197,z0,z2,z3,z68]),(0,[z1071,z0,z1,z2,z3,z6]),(0,[z17,z173,z1,z2,z3,z6]),(0,[z0,z1,z111,z2,z279,z103]),(0,[z17,z1072,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1073,z6]),(0,[z0,z1,z2,z26,z4,z6]),(0,[z0,z1,z2,z4,z6,z1074]),(0,[z0,z1,z170,z569,z4,z6]),(0,[z0,z1,z2,z3,z1075,z6]),(0,[z0,z1,z2,z3,z6,z1076])],[(0,[z0,z1,z2,z3,z1077,z6]),(0,[z0,z114,z2,z3,z104,z6]),(0,[z0,z1,z2,z179,z6,z33]),(0,[z0,z1,z2,z3,z1078,z6]),(0,[z251,z0,z649,z2,z4,z6]),(0,[z1079,z0,z1,z2,z3,z6]),(0,[z1080,z0,z1,z2,z3,z6]),(0,[z1,z170,z298,z131,z4,z6])],[(0,[z1081,z0,z1,z2,z3,z6]),(0,[z0,z1,z1082,z2,z3,z6]),(0,[z0,z1,z1083,z2,z3,z6]),(0,[z1084,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1085,z6]),(0,[z1086,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1087,z6]),(0,[z0,z1,z2,z255,z43,z6]),(0,[z0,z1,z2,z3,z1088,z6]),(0,[z173,z1,z11,z2,z3,z6]),(0,[z0,z1,z170,z11,z131,z6]),(0,[z0,z1089,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1090]),(0,[z0,z1,z1091,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1092,z6]),(0,[z1,z2,z3,z821,z4,z6]),(0,[z1093,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z757,z6]),(0,[z172,z1,z11,z2,z3,z6]),(0,[z0,z1,z2,z3,z1094,z6]),(0,[z0,z1,z2,z3,z1095,z6]),(0,[z0,z1,z2,z3,z373,z33]),(0,[z0,z1,z46,z11,z3,z6])],[(0,[z1096,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1097,z6]),(0,[z23,z484,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z162,z33]),(0,[z149,z0,z1,z2,z3,z6]),(0,[z0,z1,z170,z2,z3,z1040]),(0,[z0,z1,z2,z3,z6,z1098]),(0,[z0,z1,z79,z378,z2,z6])],[(0,[z0,z1,z2,z3,z1099,z6]),(0,[z0,z1,z2,z3,z1100,z6]),(0,[z0,z1,z765,z3,z4,z6])]],
   [[(0,[z0,z1,z1101,z3,z4,z6]),(0,[z0,z1,z2,z3,z1102,z6]),(0,[z133,z1,z1103,z3,z4,z6]),(0,[z133,z1,z42,z3,z16,z6]),(0,[z0,z510,z218,z3,z4,z6]),(0,[z683,z0,z1,z170,z4,z6]),(0,[z0,z1,z3,z16,z907,z6]),(0,[z0,z1,z2,z3,z166,z33]),(0,[z197,z0,z2,z3,z33,z68]),(0,[z1104,z0,z1,z2,z3,z6])],[(0,[z80,z0,z443,z2,z3,z6]),(0,[z0,z1,z2,z3,z1105,z6]),(0,[z1106,z0,z1,z2,z3,z6]),(0,[z20,z1,z11,z2,z49,z6]),(0,[z308,z1,z2,z3,z315,z6]),(0,[z8,z173,z1,z2,z3,z6]),(0,[z0,z1,z170,z2,z9,z6]),(0,[z141,z0,z377,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1107,z6]),(0,[z0,z1,z2,z3,z1108,z6]),(0,[z0,z1,z1109,z2,z3,z6]),(0,[z1,z74,z298,z2,z3,z6]),(0,[z29,z0,z999,z2,z3,z6])],[(0,[z0,z1,z1110,z2,z3,z6]),(0,[z23,z159,z1,z2,z3,z6]),(0,[z94,z1,z2,z3,z45,z6]),(0,[z0,z254,z377,z2,z3,z6]),(0,[z0,z1,z111,z2,z16,z103]),(0,[z0,z1,z3,z16,z922,z6]),(0,[z0,z1,z2,z1111,z14,z6]),(0,[z0,z1,z2,z3,z4,z1040]),(0,[z0,z1,z2,z3,z1112,z6])],[(0,[z0,z1,z2,z3,z1113,z6]),(0,[z0,z1,z1114,z2,z3,z6]),(0,[z0,z1,z765,z2,z4,z6]),(0,[z0,z1,z2,z3,z437,z6])],[(0,[z0,z1,z2,z3,z1115,z6]),(0,[z8,z0,z510,z2,z3,z6]),(0,[z0,z1,z11,z2,z26,z6]),(0,[z0,z1,z1116,z2,z3,z6]),(0,[z1117,z0,z1,z2,z3,z6]),(0,[z0,z40,z2,z3,z206,z33]),(0,[z57,z0,z1,z2,z3,z1040]),(0,[z0,z2,z44,z3,z244,z6]),(0,[z0,z1,z2,z3,z1118,z6])],[(0,[z0,z1,z2,z3,z1119,z6]),(0,[z0,z1,z2,z1120,z3,z6]),(0,[z0,z1,z218,z3,z6,z33]),(0,[z983,z1,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z1121,z6]),(0,[z17,z360,z0,z2,z3,z6])],[(0,[z1122,z0,z1,z2,z3,z6]),(0,[z17,z0,z1,z2,z3,z575]),(0,[z0,z1,z11,z218,z3,z6]),(0,[z0,z1,z2,z3,z1123,z6]),(0,[z0,z1,z1124,z3,z4,z6]),(0,[z17,z251,z0,z2,z13,z6]),(0,[z17,z172,z1,z2,z3,z6]),(0,[z17,z0,z785,z2,z3,z6])]],
   [[(0,[z1,z2,z1103,z3,z4,z6]),(0,[z0,z1125,z2,z3,z4,z6]),(0,[z29,z0,z1,z2,z179,z6]),(0,[z1126,z0,z1,z2,z3,z6]),(0,[z0,z170,z244,z131,z4,z6]),(0,[z17,z0,z1,z2,z3,z175])],[(0,[z556,z0,z1,z190,z3,z6]),(0,[z1127,z0,z1,z2,z3,z6]),(0,[z0,z2,z892,z3,z4,z6]),(0,[z1128,z0,z1,z2,z3,z6]),(0,[z536,z0,z2,z3,z16,z6]),(0,[z0,z1,z657,z2,z3,z33]),(0,[z0,z1,z763,z3,z6,z33])],[(0,[z0,z114,z2,z3,z4,z6]),(0,[z17,z133,z1,z42,z3,z6]),(0,[z1129,z0,z1,z2,z3,z6]),(0,[z843,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z274,z6]),(0,[z0,z1,z297,z3,z1013,z6]),(0,[z0,z1,z63,z3,z16,z136]),(0,[z360,z0,z170,z2,z4,z6]),(0,[z156,z0,z2,z3,z6,z198])],[(0,[z1130,z0,z1,z2,z3,z6]),(0,[z0,z1,z523,z2,z4,z103]),(0,[z0,z1,z218,z44,z3,z6]),(0,[z0,z1,z2,z26,z50,z6]),(0,[z0,z1,z2,z179,z104,z6]),(0,[z0,z1,z2,z3,z1131,z6]),(0,[z0,z1,z1132,z2,z3,z6]),(0,[z0,z1,z2,z3,z1133,z6]),(0,[z1134,z0,z1,z2,z3,z6]),(0,[z0,z1,z135,z2,z3,z230]),(0,[z1135,z0,z1,z2,z3,z6])],[(0,[z1136,z0,z1,z2,z3,z6]),(0,[z0,z1,z1137,z3,z4,z6]),(0,[z0,z1,z2,z1138,z3,z6]),(0,[z549,z0,z1,z11,z3,z6]),(0,[z0,z1,z2,z3,z1139,z6]),(0,[z0,z999,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1140,z6]),(0,[z0,z1,z400,z3,z6,z448])],[(0,[z0,z1,z1141,z2,z3,z4]),(0,[z0,z510,z2,z3,z1024,z6]),(0,[z0,z1,z234,z2,z3,z6]),(0,[z82,z0,z296,z55,z3,z6]),(0,[z0,z2,z238,z3,z129,z6]),(0,[z0,z1,z1142,z2,z3,z6]),(0,[z0,z1,z1143,z2,z3,z6])],[(0,[z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z462,z6]),(0,[z0,z1144,z2,z3,z4,z6]),(0,[z23,z1,z2,z3,z67,z6]),(0,[z8,z360,z0,z2,z3,z6]),(0,[z0,z1,z11,z2,z1145,z6]),(0,[z1146,z0,z1,z2,z3,z6]),(0,[z263,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z6,z33]),(0,[z0,z1,z2,z3,z1147,z6]),(0,[z1148,z0,z1,z2,z3,z6]),(0,[z1149,z0,z1,z2,z3,z6]),(0,[z0,z443,z2,z3,z14,z6]),(0,[z8,z172,z1,z2,z3,z6]),(0,[z173,z1,z170,z131,z4,z6]),(0,[z57,z719,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1150])]],
   [[(0,[z1151,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1152,z6]),(0,[z0,z1,z1153,z2,z3,z6]),(0,[z1,z2,z3,z87,z857,z6]),(1,[z82,z0,z628,z4,z6]),(0,[z291,z0,z1,z2,z3,z6]),(0,[z346,z0,z2,z3,z16,z6]),(0,[z0,z1,z170,z234,z3,z6]),(0,[z149,z0,z1,z2,z3,z163]),(0,[z0,z1,z2,z3,z1154,z6]),(0,[z0,z1155,z2,z3,z4,z6]),(0,[z29,z0,z2,z3,z244,z6]),(0,[z1156,z0,z1,z2,z3,z6]),(0,[z0,z1,z1157,z2,z3,z6]),(0,[z0,z1,z2,z6,z739,z142])],[(0,[z133,z1,z42,z3,z4,z6]),(0,[z0,z1,z1158,z2,z3,z6]),(0,[z0,z1,z2,z296,z3,z6]),(0,[z291,z251,z0,z2,z13,z6]),(0,[z0,z1,z2,z3,z6,z1159]),(0,[z1160,z0,z1,z2,z3,z6]),(0,[z360,z0,z2,z3,z1161,z6]),(0,[z977,z0,z2,z3,z244,z6]),(0,[z0,z1,z2,z3,z1162,z6]),(0,[z0,z1,z2,z3,z1163,z6])],[(0,[z0,z1,z631,z3,z4,z136]),(0,[z0,z1,z281,z11,z3,z6]),(0,[z468,z0,z1,z2,z3,z6]),(0,[z0,z15,z1,z2,z3,z33]),(0,[z0,z1,z731,z2,z3,z33])],[(0,[z1,z2,z3,z16,z6,z877]),(1,[z0,z924,z2,z3,z6]),(0,[z0,z1,z1164,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1165]),(0,[z0,z1,z1166,z2,z3,z6])],[(0,[z0,z1,z2,z44,z3,z6]),(0,[z1058,z0,z2,z3,z4,z6]),(0,[z82,z251,z0,z170,z4,z6]),(0,[z0,z1,z2,z3,z1167,z6]),(0,[z0,z1,z111,z2,z4,z103])],[(0,[z454,z0,z1,z2,z44,z6]),(0,[z0,z1,z731,z2,z3,z78])],[(0,[z0,z1,z1168,z3,z4,z6]),(0,[z0,z1,z2,z3,z1169,z6]),(0,[z0,z1,z2,z3,z1170,z6]),(0,[z0,z1,z2,z3,z1171,z6]),(0,[z0,z1,z218,z3,z104,z6]),(0,[z0,z1,z2,z1172,z3,z6]),(0,[z0,z1,z2,z3,z1173,z6]),(0,[z17,z0,z1,z2,z3,z604]),(0,[z0,z1,z2,z1174,z6,z198]),(0,[z0,z1,z2,z4,z6,z739])],[(0,[z0,z1,z2,z3,z1175,z6]),(0,[z0,z1,z2,z1176,z4,z6]),(0,[z0,z114,z11,z2,z3,z6]),(0,[z0,z1,z763,z3,z16,z6]),(0,[z983,z1,z2,z3,z4,z6]),(0,[z1,z298,z2,z3,z14,z6]),(0,[z0,z2,z3,z221,z6,z68]),(0,[z0,z1,z2,z3,z1177,z6]),(0,[z0,z1,z100,z2,z9,z6]),(0,[z0,z1,z46,z466,z3,z6])]],
   [[(0,[z0,z510,z2,z26,z4,z6]),(0,[z0,z1,z3,z6,z1178,z107]),(0,[z0,z1,z63,z11,z3,z136])],[(0,[z0,z1,z1179,z2,z3,z6]),(0,[z82,z0,z1,z628,z4,z6]),(0,[z0,z2,z3,z730,z244,z6]),(0,[z0,z1,z2,z3,z1180,z6]),(0,[z0,z1,z1181,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1182,z6]),(0,[z0,z1,z1183,z2,z3,z6]),(0,[z0,z1,z2,z3,z1184,z6]),(0,[z0,z1,z48,z2,z3,z264])],[(0,[z0,z114,z2,z3,z50,z6]),(0,[z25,z1,z2,z26,z4,z185]),(0,[z0,z1,z2,z3,z1185,z6]),(0,[z0,z158,z2,z3,z14,z6]),(0,[z197,z0,z2,z3,z4,z893]),(0,[z29,z1,z298,z2,z3,z6]),(0,[z0,z1,z2,z3,z1186,z6])],[(0,[z1187,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1188,z6]),(0,[z1,z1103,z42,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z1189]),(0,[z0,z2,z3,z4,z1190,z6]),(0,[z57,z0,z1,z509,z3,z6]),(0,[z0,z1,z2,z4,z767,z103])],[(0,[z0,z1,z2,z3,z16,z6]),(0,[z29,z0,z1,z2,z270,z6]),(0,[z0,z1,z2,z3,z1191,z6]),(0,[z0,z1,z1192,z2,z3,z6]),(0,[z0,z1,z2,z3,z1193,z6]),(0,[z0,z1,z1194,z3,z16,z6]),(0,[z0,z1,z2,z3,z221,z6]),(0,[z0,z1,z2,z1195,z3,z6])],[(0,[z0,z1196,z2,z3,z4,z6]),(0,[z1197,z0,z1,z2,z3,z6]),(0,[z1198,z0,z1,z2,z3,z6]),(0,[z1199,z0,z1,z2,z3,z6]),(0,[z0,z649,z2,z3,z16,z6]),(0,[z0,z2,z303,z3,z16,z6]),(0,[z0,z1,z48,z2,z44,z309])],[(0,[z1200,z0,z1,z2,z3,z6]),(0,[z1201,z0,z1,z2,z3,z6]),(0,[z1202,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z104,z6]),(0,[z0,z1,z2,z782,z179,z6]),(0,[z0,z1,z2,z1203,z3,z6]),(0,[z0,z1,z2,z1204,z3,z6]),(0,[z0,z1,z2,z3,z498,z6]),(0,[z0,z1,z1205,z2,z3,z6]),(0,[z1206,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1207,z6]),(0,[z0,z1,z2,z3,z1208,z6]),(0,[z0,z691,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z1209,z6])]],
   [[(0,[z1210,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1211,z6]),(0,[z0,z1,z2,z1212,z4,z6]),(0,[z0,z1,z2,z3,z1213,z6]),(0,[z1214,z0,z1,z2,z3,z6]),(0,[z0,z1,z1215,z2,z16,z6]),(0,[z0,z1,z2,z3,z1216,z6]),(0,[z0,z1,z2,z3,z1217,z6]),(0,[z360,z0,z100,z2,z4,z6]),(0,[z336,z0,z1,z2,z3,z6]),(0,[z0,z1218,z1,z2,z3,z6])],[(0,[z0,z1,z628,z2,z296,z6]),(0,[z0,z1,z940,z2,z3,z6]),(0,[z1219,z0,z1,z2,z3,z6]),(0,[z0,z1,z416,z3,z6,z136])],[(0,[z0,z1,z2,z3,z4,z1220]),(0,[z0,z1,z2,z1221,z4,z6]),(0,[z0,z1,z2,z1222,z3,z6]),(0,[z0,z1,z2,z3,z1223,z6]),(0,[z0,z1,z2,z3,z33,z157]),(0,[z29,z1,z2,z3,z6,z248]),(0,[z0,z1,z2,z3,z1224,z6])],[(0,[z250,z1,z42,z3,z4,z6]),(0,[z0,z1225,z2,z3,z4,z6]),(0,[z0,z1,z2,z1111,z4,z6]),(0,[z168,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1226,z6]),(0,[z0,z1,z2,z1227,z3,z6]),(0,[z148,z1,z2,z3,z521,z6]),(0,[z0,z1,z111,z11,z2,z103]),(0,[z0,z1,z2,z3,z1228,z6])],[(0,[z0,z1,z2,z3,z1229,z6]),(0,[z0,z1,z48,z2,z300,z6])],[(0,[z0,z1,z2,z3,z1230,z6]),(0,[z0,z1,z2,z3,z1231,z6]),(0,[z0,z1,z2,z3,z1232,z6]),(0,[z94,z1,z2,z3,z87,z6]),(0,[z1,z298,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z1233,z6]),(0,[z173,z1,z2,z3,z1234,z6]),(0,[z0,z2,z3,z244,z223,z6]),(0,[z0,z1,z2,z1235,z3,z6]),(0,[z0,z1,z63,z2,z3,z171]),(0,[z17,z0,z1,z2,z3,z490])],[(0,[z0,z1236,z2,z3,z4,z6]),(0,[z0,z1,z11,z53,z3,z6]),(0,[z1237,z0,z1,z2,z3,z6]),(0,[z1238,z0,z1,z2,z3,z6])]],
   [[(0,[z1239,z0,z2,z3,z4,z6]),(0,[z29,z0,z1,z2,z26,z6]),(0,[z0,z1,z2,z3,z1240,z6]),(0,[z0,z377,z2,z3,z13,z6]),(0,[z468,z0,z1,z100,z2,z6]),(0,[z0,z1,z763,z3,z4,z6]),(0,[z0,z1,z170,z44,z131,z6]),(0,[z0,z1,z2,z3,z1241,z6]),(0,[z0,z1,z2,z1242,z3,z6]),(0,[z0,z1,z2,z1243,z3,z6]),(0,[z17,z0,z1,z2,z3,z33])],[(0,[z1,z2,z3,z4,z6,z248]),(0,[z1244,z0,z1,z2,z3,z6]),(0,[z28,z0,z158,z2,z3,z6]),(0,[z0,z1,z2,z3,z1245,z6]),(0,[z0,z2,z3,z221,z6,z198]),(0,[z29,z0,z1,z2,z6,z372]),(0,[z0,z1,z416,z2,z3,z6]),(0,[z0,z1,z1246,z2,z3,z6])],[(0,[z23,z527,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1247,z6]),(0,[z156,z0,z2,z3,z16,z6]),(0,[z173,z1,z2,z3,z727,z6]),(0,[z0,z1,z174,z2,z3,z6]),(0,[z1248,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1249,z6])],[(0,[z468,z0,z1,z2,z227,z6]),(0,[z25,z114,z2,z3,z4,z185]),(0,[z0,z1,z1060,z2,z3,z6]),(0,[z0,z1,z2,z179,z50,z6]),(0,[z0,z1,z297,z3,z14,z6]),(0,[z117,z0,z1,z3,z6,z167]),(0,[z1250,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1251,z6])],[(0,[z0,z1,z2,z3,z1252,z6]),(0,[z1253,z0,z1,z2,z3,z6]),(0,[z0,z510,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z1254,z6]),(0,[z17,z0,z1,z196,z3,z6]),(0,[z0,z1,z196,z11,z3,z6]),(0,[z0,z1,z2,z3,z4,z849]),(0,[z1,z2,z3,z4,z6,z1255]),(0,[z0,z1,z400,z3,z6,z136])],[(0,[z1256,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z857,z6]),(0,[z0,z510,z2,z3,z6,z33]),(0,[z468,z0,z1,z2,z238,z6]),(0,[z0,z1,z2,z3,z1257,z6]),(0,[z0,z1,z79,z2,z6,z142]),(0,[z0,z1,z1258,z2,z3,z6])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z1259,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1260,z6]),(0,[z1,z1261,z2,z3,z4,z6]),(0,[z0,z1,z1194,z3,z4,z6]),(0,[z1,z2,z3,z6,z248,z198]),(0,[z57,z0,z1,z2,z3,z849]),(0,[z0,z1,z1262,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1263,z6]),(0,[z29,z0,z1,z2,z6,z613]),(0,[z25,z1,z2,z3,z14,z185]),(0,[z0,z1,z2,z3,z6,z1264]),(0,[z0,z1,z2,z3,z1265,z6]),(0,[z0,z1,z1266,z3,z16,z6]),(0,[z8,z0,z1,z416,z3,z6]),(0,[z0,z1,z2,z3,z1267,z6]),(0,[z0,z1,z563,z2,z44,z6])]],
   [[(0,[z1268,z0,z1,z2,z3,z6]),(0,[z0,z1,z1269,z2,z3,z6]),(0,[z0,z282,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z1270,z6]),(0,[z0,z254,z1,z196,z4,z6]),(0,[z0,z1,z1271,z2,z3,z6]),(0,[z57,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1272,z6]),(0,[z0,z1,z378,z2,z3,z264])],[(0,[z148,z1,z2,z3,z87,z6]),(0,[z0,z1,z2,z1273,z4,z6]),(0,[z0,z1,z1215,z2,z4,z6]),(0,[z1274,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1275,z6]),(0,[z0,z1,z2,z3,z6,z1276]),(0,[z0,z1,z400,z3,z6,z107])],[(0,[z1277,z0,z1,z2,z3,z6]),(0,[z308,z1,z2,z3,z24,z6]),(0,[z0,z510,z2,z44,z3,z6]),(0,[z8,z0,z1,z2,z179,z6]),(0,[z556,z0,z1,z3,z6,z107]),(0,[z17,z0,z2,z3,z244,z6]),(0,[z0,z1,z11,z2,z1278,z6])],[(0,[z80,z41,z2,z3,z14,z6]),(0,[z0,z1,z628,z2,z44,z6]),(0,[z0,z1,z2,z3,z1279,z6]),(0,[z468,z0,z1,z2,z255,z6]),(0,[z149,z1066,z1,z2,z3,z6]),(0,[z0,z1,z924,z2,z3,z6]),(0,[z29,z0,z1,z2,z300,z6]),(0,[z350,z484,z1,z2,z3,z6])],[(0,[z80,z41,z2,z3,z6,z33]),(0,[z1,z675,z42,z3,z4,z6]),(0,[z1280,z0,z1,z2,z3,z6]),(0,[z1281,z0,z1,z2,z3,z6]),(0,[z82,z0,z628,z3,z4,z6]),(0,[z0,z1,z2,z303,z3,z6]),(0,[z0,z1,z2,z3,z1282,z6]),(0,[z0,z1,z869,z2,z3,z6]),(0,[z149,z1072,z1,z2,z3,z6]),(0,[z8,z0,z1,z89,z3,z6]),(0,[z0,z1,z2,z3,z1283,z6]),(0,[z0,z1,z63,z3,z437,z136])],[(0,[z0,z1,z2,z3,z1284,z6]),(0,[z1285,z0,z1,z2,z3,z6]),(0,[z133,z1,z42,z3,z6,z33]),(0,[z0,z1,z2,z1286,z3,z6]),(0,[z0,z1,z1287,z3,z4,z6]),(0,[z556,z0,z1,z2,z3,z6]),(0,[z117,z0,z1,z234,z3,z6]),(0,[z0,z1,z1288,z2,z3,z6]),(0,[z0,z1,z2,z3,z528,z163]),(0,[z0,z1,z2,z3,z6,z1289]),(0,[z0,z1,z109,z2,z3,z171]),(0,[z0,z1,z1137,z44,z3,z6]),(0,[z1290,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z1291,z3,z6]),(0,[z0,z1,z218,z3,z50,z6]),(0,[z0,z1,z147,z2,z3,z6]),(0,[z1292,z0,z1,z2,z3,z6]),(0,[z1293,z1,z2,z3,z4,z6]),(0,[z291,z0,z1,z196,z3,z6]),(0,[z1294,z0,z1,z2,z3,z6]),(0,[z1295,z0,z1,z2,z3,z6]),(0,[z197,z0,z2,z3,z177,z68]),(0,[z188,z0,z1,z2,z3,z230]),(0,[z0,z1,z2,z3,z6,z1178])],[(0,[z0,z1,z2,z1296,z3,z6]),(0,[z1,z298,z2,z3,z4,z6]),(0,[z0,z1,z1297,z2,z3,z6]),(0,[z0,z1,z2,z3,z1298,z6]),(0,[z0,z102,z2,z3,z16,z6]),(0,[z360,z0,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z1299,z6]),(0,[z0,z1,z1300,z2,z3,z6])]],
   [[(0,[z0,z1,z2,z1301,z3,z6]),(0,[z0,z510,z2,z179,z4,z6]),(0,[z0,z1,z2,z3,z6,z1302]),(0,[z0,z1,z2,z1303,z3,z6]),(0,[z0,z1,z2,z3,z6,z1304]),(0,[z0,z1,z2,z3,z1305,z6]),(0,[z956,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1306,z6]),(0,[z360,z0,z2,z3,z6,z33])],[(0,[z1307,z0,z1,z2,z3,z6]),(0,[z80,z41,z2,z44,z3,z6]),(0,[z0,z1,z2,z1308,z3,z6]),(0,[z0,z1,z2,z1309,z3,z6]),(0,[z172,z1,z2,z3,z6,z198]),(0,[z0,z1,z2,z3,z1310,z6]),(0,[z0,z2,z3,z4,z6,z1311])],[(0,[z29,z80,z41,z2,z3,z6]),(0,[z0,z1,z2,z3,z1312,z6]),(0,[z133,z1,z42,z44,z3,z6]),(0,[z1313,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1314,z6]),(0,[z1315,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z1316,z3,z6]),(0,[z0,z1,z297,z3,z16,z6]),(0,[z0,z1,z1317,z2,z3,z6]),(0,[z0,z1,z2,z3,z1318,z6]),(0,[z0,z1,z1319,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z759])],[(0,[z0,z1,z11,z2,z3,z6]),(0,[z0,z510,z2,z3,z16,z6]),(0,[z25,z1,z2,z179,z4,z185]),(0,[z65,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1320,z6]),(0,[z0,z1,z2,z3,z1321,z6]),(0,[z0,z1,z2,z1322,z3,z6]),(0,[z0,z1,z2,z3,z33,z682]),(0,[z0,z1,z1323,z2,z3,z6]),(0,[z983,z1,z2,z3,z6,z33])],[(0,[z1324,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1325,z6]),(0,[z0,z1,z54,z2,z296,z6]),(0,[z291,z0,z1,z297,z3,z6]),(0,[z405,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z1326,z3,z6]),(0,[z0,z1,z1327,z3,z4,z6]),(0,[z0,z1,z2,z3,z1328,z6]),(0,[z0,z1,z2,z3,z37,z6]),(0,[z0,z1,z1329,z2,z3,z6]),(0,[z0,z1,z1330,z2,z3,z6]),(0,[z17,z1,z298,z2,z3,z6]),(0,[z360,z0,z2,z44,z3,z6]),(0,[z29,z0,z1,z2,z646,z6])],[(0,[z0,z1,z2,z3,z6,z1331]),(0,[z553,z20,z1,z2,z49,z6]),(0,[z0,z1,z2,z3,z6,z1332]),(0,[z25,z1,z2,z3,z16,z185]),(0,[z251,z0,z196,z2,z4,z6]),(0,[z0,z1,z63,z3,z14,z136]),(0,[z134,z527,z1,z2,z3,z6]),(0,[z1333,z0,z1,z2,z3,z6]),(0,[z0,z1,z1334,z2,z3,z6])],[(0,[z1058,z41,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z50,z6]),(0,[z25,z8,z1,z2,z3,z185]),(0,[z0,z1,z2,z3,z1335,z6]),(0,[z0,z1,z1336,z2,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z1337,z6]),(0,[z0,z1,z1266,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z1338]),(0,[z17,z0,z510,z2,z3,z6]),(0,[z1339,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1340]),(0,[z468,z0,z1,z2,z44,z6]),(0,[z360,z0,z2,z3,z1177,z6]),(0,[z0,z1,z2,z3,z58,z6])],[(0,[z0,z1,z2,z3,z6,z1341]),(0,[z8,z0,z1,z581,z3,z6]),(0,[z0,z1,z2,z3,z62,z6]),(0,[z0,z1,z3,z4,z6,z1342]),(0,[z0,z1,z2,z3,z1343,z6]),(0,[z0,z1,z39,z2,z6,z142]),(0,[z0,z1,z2,z3,z33,z264])],[(0,[z80,z41,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z1344,z6]),(0,[z0,z1,z2,z3,z1345,z6]),(0,[z468,z0,z1,z2,z13,z6]),(0,[z0,z254,z1,z79,z2,z6]),(0,[z0,z1,z1346,z2,z3,z14]),(0,[z149,z172,z1,z2,z3,z6]),(0,[z0,z1,z398,z11,z3,z6]),(0,[z0,z1,z3,z922,z6,z33])],[(0,[z0,z1,z2,z3,z1347,z6]),(0,[z0,z1,z2,z3,z1348,z6]),(0,[z1349,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z9,z3,z6]),(0,[z1350,z0,z1,z2,z3,z6]),(0,[z8,z0,z1,z3,z6,z1178]),(0,[z29,z0,z1,z2,z317,z6]),(0,[z0,z1,z1351,z2,z3,z6])],[(0,[z1352,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1353,z6]),(0,[z0,z1,z2,z3,z206,z163]),(0,[z17,z1,z2,z3,z6,z248]),(0,[z0,z1,z1354,z2,z3,z6]),(0,[z0,z1,z63,z44,z3,z136]),(0,[z0,z1,z2,z3,z1355,z6])],[(0,[z8,z1,z298,z2,z3,z6])],[(0,[z25,z1,z218,z3,z4,z185]),(0,[z0,z1,z3,z4,z1356,z6]),(0,[z360,z0,z2,z3,z16,z6]),(0,[z1357,z0,z1,z2,z3,z6]),(0,[z0,z1,z74,z170,z131,z6]),(0,[z0,z1,z46,z30,z3,z6]),(0,[z0,z1,z2,z3,z6,z1358]),(0,[z1359,z0,z1,z2,z3,z6])],[(0,[z0,z1,z1360,z2,z3,z6]),(0,[z0,z114,z2,z3,z1361,z6]),(0,[z0,z1,z2,z3,z6,z1362]),(0,[z0,z1,z54,z2,z1363,z6]),(0,[z0,z1,z2,z3,z1364,z6])]],
   [[(0,[z1365,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1366]),(0,[z0,z1,z2,z3,z1367,z6]),(0,[z0,z1,z297,z11,z3,z6]),(0,[z0,z1,z1368,z2,z3,z6]),(0,[z0,z1,z1369,z2,z3,z6]),(0,[z449,z414,z1,z2,z3,z6])],[(0,[z0,z1,z2,z1370,z4,z6]),(0,[z0,z1,z2,z3,z1371,z6]),(0,[z0,z1,z2,z3,z1372,z6]),(0,[z0,z1,z2,z3,z1373,z6]),(0,[z0,z1,z2,z3,z1374,z6]),(0,[z29,z82,z0,z55,z3,z6]),(0,[z0,z1,z2,z3,z6,z1375]),(0,[z1072,z1,z2,z3,z14,z6]),(0,[z0,z1,z1376,z2,z3,z6]),(0,[z0,z1,z1377,z2,z3,z6]),(0,[z0,z1,z2,z3,z1378,z6]),(0,[z0,z1,z2,z3,z1379,z6])],[(0,[z29,z0,z1,z53,z3,z6]),(0,[z25,z0,z1,z2,z3,z163]),(0,[z0,z1,z2,z3,z6,z1380]),(0,[z0,z1,z1381,z2,z3,z6]),(0,[z556,z0,z1,z55,z3,z6]),(0,[z0,z1,z2,z3,z6,z1382]),(0,[z0,z1,z443,z2,z3,z6])],[(0,[z0,z1,z1383,z2,z3,z6]),(0,[z0,z1,z11,z144,z3,z6]),(0,[z0,z1,z2,z3,z1384,z6]),(0,[z0,z1,z297,z3,z4,z6]),(0,[z0,z1,z2,z3,z1385,z6]),(0,[z0,z1,z2,z538,z44,z6]),(0,[z1386,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z110,z6]),(0,[z1387,z0,z1,z2,z3,z6])],[(0,[z1388,z0,z1,z2,z3,z6]),(0,[z0,z510,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z1389]),(0,[z0,z1,z2,z3,z6,z1390]),(0,[z0,z1,z2,z3,z1391,z6]),(0,[z0,z1,z2,z3,z314,z6]),(0,[z8,z1,z2,z3,z6,z248]),(0,[z0,z1,z2,z3,z1392,z6])],[(0,[z0,z1,z2,z3,z1393,z6]),(0,[z0,z1,z2,z3,z1394,z6]),(0,[z0,z1,z2,z3,z1395,z6]),(0,[z0,z1,z2,z600,z44,z6]),(0,[z82,z0,z576,z3,z4,z6]),(0,[z0,z1,z2,z3,z1396,z6])],[(0,[z0,z1,z2,z3,z120,z6]),(0,[z0,z1,z2,z3,z4,z1397]),(0,[z0,z1,z606,z2,z3,z33]),(0,[z0,z1,z2,z3,z6,z1398]),(0,[z117,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z1399,z3,z6]),(0,[z82,z0,z628,z55,z4,z6]),(0,[z0,z1,z54,z2,z44,z6]),(0,[z0,z1,z2,z796,z4,z6]),(0,[z0,z1,z2,z3,z1400,z6]),(0,[z0,z1,z2,z3,z1401,z6]),(0,[z57,z0,z999,z2,z3,z6]),(0,[z447,z1,z390,z2,z3,z6])],[(0,[z0,z1,z2,z3,z6,z1402]),(0,[z0,z1,z1403,z3,z4,z6]),(0,[z25,z1,z2,z3,z4,z185]),(0,[z0,z2,z3,z16,z6,z634]),(0,[z29,z0,z1,z2,z665,z6]),(0,[z0,z1,z1404,z2,z3,z6]),(0,[z0,z1,z765,z170,z4,z6])]],
   [[(0,[z1405,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1406,z6]),(0,[z94,z1,z2,z524,z3,z6])],[(0,[z0,z1,z2,z3,z192,z6]),(0,[z0,z1,z2,z3,z1407,z6]),(0,[z0,z1,z1408,z2,z3,z6]),(0,[z0,z1,z2,z3,z1409,z6]),(0,[z0,z1,z2,z3,z6,z1410]),(0,[z8,z0,z1,z445,z3,z6]),(0,[z1,z2,z3,z16,z6,z248])],[(0,[z0,z1,z2,z3,z1411,z6]),(0,[z0,z113,z2,z3,z16,z6]),(0,[z8,z0,z1,z2,z26,z6]),(0,[z1412,z0,z1,z2,z3,z6]),(0,[z0,z2,z796,z13,z4,z6]),(0,[z0,z1,z196,z3,z14,z6]),(0,[z0,z338,z2,z3,z16,z6]),(0,[z0,z1,z1413,z3,z14,z6]),(0,[z0,z1,z2,z1414,z3,z6]),(0,[z1415,z1,z2,z3,z6,z248]),(0,[z29,z0,z1,z170,z131,z6])],[(0,[z80,z41,z2,z3,z4,z6]),(0,[z0,z1,z1416,z2,z3,z6]),(0,[z29,z0,z1,z2,z191,z6]),(0,[z0,z1,z2,z3,z1417,z6]),(1,[z251,z0,z196,z4,z6]),(0,[z0,z1,z196,z3,z6,z33]),(0,[z0,z1,z1418,z2,z3,z6]),(0,[z0,z1,z2,z3,z1419,z6]),(0,[z29,z0,z924,z2,z3,z6]),(0,[z263,z0,z1,z2,z3,z175])],[(0,[z0,z1,z2,z3,z1420,z6]),(0,[z0,z1,z2,z3,z1421,z6]),(0,[z1422,z0,z1,z2,z3,z6]),(0,[z0,z15,z1,z2,z3,z206]),(0,[z197,z0,z2,z3,z14,z68]),(0,[z1,z1376,z298,z2,z3,z6]),(0,[z0,z1,z1423,z2,z3,z6]),(0,[z29,z799,z1,z2,z3,z6]),(0,[z0,z1,z2,z1424,z3,z6]),(0,[z29,z0,z1,z2,z6,z142])],[(0,[z0,z1,z2,z3,z4,z1425]),(0,[z1,z526,z2,z49,z4,z6]),(0,[z0,z1,z2,z3,z1426,z6]),(0,[z1427,z0,z1,z2,z3,z6]),(0,[z8,z0,z1,z174,z3,z6])],[(0,[z0,z1,z2,z3,z1428,z6]),(0,[z0,z1,z2,z3,z1429,z6]),(0,[z0,z1,z2,z3,z1430,z6]),(0,[z173,z1,z74,z2,z3,z6]),(0,[z476,z0,z1,z2,z3,z6])],[(0,[z1431,z0,z1,z2,z3,z6]),(0,[z8,z0,z1,z519,z3,z6]),(0,[z360,z0,z2,z3,z4,z6]),(0,[z0,z1,z892,z3,z4,z6]),(0,[z8,z0,z1,z54,z2,z6]),(0,[z0,z1,z2,z3,z1432,z6]),(0,[z0,z1,z2,z3,z6,z1433]),(0,[z0,z1,z2,z3,z1434,z6]),(0,[z0,z1,z2,z3,z1435,z6]),(0,[z0,z1,z2,z1436,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z1437,z6]),(0,[z0,z1,z196,z44,z3,z6]),(0,[z0,z1,z2,z1438,z16,z6]),(0,[z0,z1,z2,z3,z1439,z6]),(0,[z29,z0,z1,z2,z666,z6]),(0,[z0,z1,z3,z4,z6,z1178])],[(0,[z0,z1,z1440,z3,z4,z6]),(0,[z664,z0,z2,z3,z16,z6]),(0,[z0,z1,z1441,z2,z3,z6]),(0,[z1442,z0,z1,z2,z3,z6]),(0,[z0,z1,z1443,z2,z3,z6]),(0,[z0,z1,z1444,z2,z3,z6]),(0,[z17,z0,z1445,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1446,z6]),(0,[z0,z1,z2,z3,z1447,z6]),(0,[z0,z1,z2,z3,z1448,z6]),(0,[z0,z1,z1449,z2,z3,z6]),(0,[z468,z0,z1,z111,z2,z6]),(0,[z0,z1,z400,z109,z3,z6]),(0,[z0,z1,z2,z3,z480,z6]),(0,[z0,z1,z111,z2,z3,z264])],[(0,[z1,z2,z3,z4,z6,z1450]),(0,[z0,z1,z2,z3,z6,z1451]),(0,[z0,z1,z1452,z2,z3,z6]),(0,[z0,z354,z2,z3,z16,z6]),(0,[z947,z1,z298,z2,z3,z6]),(0,[z1,z298,z2,z3,z6,z33]),(0,[z1453,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1454,z6])],[(0,[z0,z1455,z2,z3,z4,z6]),(0,[z0,z1456,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z125,z6]),(0,[z0,z2,z3,z16,z221,z6]),(0,[z17,z0,z1,z557,z2,z3])],[(0,[z0,z1,z2,z3,z6,z1457]),(0,[z0,z1,z1458,z2,z3,z6]),(0,[z1459,z0,z1,z2,z3,z6]),(0,[z0,z2,z3,z129,z16,z6]),(0,[z0,z1,z2,z3,z1460,z6]),(0,[z0,z1,z2,z3,z1461,z6])],[(0,[z0,z1,z2,z3,z181,z6]),(0,[z23,z1,z2,z3,z24,z6]),(1,[z1,z2,z3,z857,z6]),(0,[z0,z1,z53,z26,z4,z6]),(0,[z25,z17,z1,z2,z3,z185]),(0,[z1462,z0,z1,z2,z3,z6]),(0,[z0,z1,z31,z2,z44,z6]),(0,[z0,z1,z63,z3,z4,z136])],[(0,[z0,z1,z2,z1463,z4,z6]),(0,[z8,z0,z1,z351,z3,z6]),(0,[z0,z1,z2,z3,z6,z1464]),(0,[z0,z1,z2,z43,z13,z6]),(0,[z0,z1,z1465,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1466])]],
   [[(0,[z80,z41,z11,z2,z3,z6]),(0,[z72,z172,z2,z3,z4,z6]),(0,[z29,z0,z1,z628,z2,z6]),(0,[z0,z1,z2,z3,z1467,z6]),(0,[z556,z0,z1,z147,z3,z6]),(0,[z0,z1,z2,z3,z1468,z6]),(0,[z168,z0,z1,z2,z43,z6]),(0,[z0,z1,z1469,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1470]),(0,[z1,z298,z2,z44,z3,z6])],[(0,[z0,z1,z1471,z2,z3,z6]),(0,[z0,z1,z196,z3,z16,z6]),(0,[z1066,z1,z2,z3,z14,z6]),(0,[z956,z1,z2,z44,z3,z6]),(0,[z0,z1,z2,z1472,z3,z6])],[(0,[z453,z0,z1,z2,z3,z33]),(0,[z1473,z0,z1,z2,z3,z6]),(0,[z556,z0,z1,z3,z69,z6]),(0,[z0,z1,z2,z3,z1474,z6])],[(0,[z0,z1,z2,z3,z1475,z6]),(0,[z0,z1,z2,z3,z6,z1476]),(0,[z0,z36,z51,z11,z3,z6]),(0,[z197,z0,z2,z3,z16,z68]),(0,[z0,z1,z1477,z2,z3,z6]),(0,[z0,z1,z1478,z2,z3,z6]),(0,[z0,z1,z2,z3,z367,z6]),(0,[z0,z1,z2,z3,z78,z175])],[(0,[z8,z80,z41,z2,z3,z6]),(0,[z0,z1,z39,z2,z227,z6]),(0,[z0,z1445,z2,z3,z4,z6]),(0,[z1479,z0,z1,z2,z3,z6]),(0,[z0,z1,z11,z622,z3,z6]),(0,[z0,z1,z2,z1480,z3,z6]),(1,[z360,z0,z170,z4,z6]),(0,[z1481,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1482]),(0,[z0,z1,z2,z3,z1483,z6]),(0,[z0,z1,z1484,z2,z3,z6]),(0,[z0,z1,z1485,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1486])],[(0,[z1058,z1,z2,z3,z4,z6]),(0,[z0,z1,z1487,z2,z3,z6]),(0,[z0,z2,z3,z16,z6,z231]),(0,[z0,z1,z2,z3,z1488,z6]),(0,[z1489,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1234,z6]),(0,[z0,z1,z2,z3,z212,z6])],[(0,[z1490,z0,z1,z2,z3,z6]),(0,[z0,z1,z1491,z2,z3,z6]),(0,[z0,z1492,z1,z2,z3,z6]),(0,[z0,z1,z170,z2,z43,z6]),(0,[z0,z1,z3,z14,z6,z865]),(0,[z0,z2,z3,z4,z6,z893]),(0,[z0,z1,z869,z2,z6,z68]),(0,[z57,z173,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1493,z6]),(0,[z0,z1,z2,z3,z1494,z6])],[(0,[z0,z1,z2,z3,z1495,z6]),(0,[z29,z20,z1,z2,z49,z6]),(0,[z0,z1,z2,z3,z4,z1450]),(0,[z251,z0,z2,z3,z129,z6])]],
   [[(0,[z133,z1,z11,z42,z3,z6]),(0,[z1496,z0,z1,z2,z3,z6]),(0,[z0,z1497,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1498]),(0,[z0,z1,z2,z3,z516,z6]),(0,[z0,z1,z48,z2,z309,z33])],[(0,[z0,z1,z2,z1438,z4,z6]),(0,[z0,z1,z2,z3,z1499,z6]),(0,[z82,z0,z54,z55,z4,z6]),(0,[z0,z377,z51,z2,z3,z6]),(0,[z251,z0,z2,z13,z14,z6]),(0,[z1072,z1,z2,z3,z4,z6]),(0,[z1500,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1501,z6]),(0,[z0,z1,z2,z3,z6,z1502]),(0,[z0,z1,z2,z3,z1503,z6]),(0,[z0,z1,z1504,z44,z3,z6]),(0,[z0,z1,z1505,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1506,z6]),(0,[z0,z1,z1507,z53,z3,z6]),(0,[z0,z1,z2,z3,z1508,z6]),(0,[z1,z2,z44,z3,z6,z248]),(0,[z360,z0,z1,z170,z4,z6]),(0,[z0,z1,z2,z3,z1509,z6]),(0,[z1,z997,z2,z44,z3,z6]),(0,[z0,z1,z2,z3,z1510,z6])],[(0,[z0,z1,z2,z3,z1511,z6]),(0,[z0,z1,z2,z1512,z3,z6]),(0,[z0,z1,z2,z3,z1361,z6]),(0,[z0,z1,z2,z3,z1513,z6]),(0,[z0,z1,z1514,z2,z3,z6]),(0,[z0,z1,z1515,z2,z3,z6]),(0,[z8,z0,z1,z618,z3,z6]),(0,[z0,z1,z2,z1174,z6,z33])],[(0,[z0,z1516,z2,z3,z4,z6]),(0,[z0,z1,z2,z1517,z3,z6]),(0,[z0,z1,z2,z1518,z3,z6])],[(0,[z0,z1,z2,z3,z1519,z6]),(0,[z0,z1,z1520,z2,z3,z6]),(0,[z0,z1,z2,z1521,z4,z6]),(0,[z29,z0,z1,z218,z3,z6]),(0,[z17,z0,z1,z2,z179,z6]),(0,[z1522,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1523,z6]),(0,[z0,z114,z53,z3,z4,z6]),(0,[z251,z0,z158,z2,z3,z6]),(0,[z0,z1,z1524,z2,z3,z6]),(0,[z172,z1,z2,z3,z1028,z6]),(0,[z188,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1525,z6]),(0,[z0,z1,z1103,z3,z4,z6]),(0,[z0,z1,z46,z42,z3,z6]),(0,[z184,z1,z190,z11,z3,z6]),(0,[z0,z2,z3,z4,z6,z1526]),(0,[z522,z1,z2,z3,z24,z6]),(0,[z0,z1,z2,z3,z33,z193]),(0,[z25,z1,z2,z3,z4,z1450]),(0,[z0,z1,z2,z3,z6,z1527]),(0,[z0,z1,z2,z4,z6,z1528]),(0,[z0,z1,z297,z3,z6,z33]),(0,[z8,z0,z1,z234,z3,z6]),(0,[z0,z1,z2,z3,z1529,z6]),(0,[z76,z159,z1,z2,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z1530,z6]),(0,[z0,z1,z2,z1531,z4,z6]),(0,[z0,z1,z2,z3,z1532,z6]),(0,[z1533,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1534]),(0,[z1535,z0,z1,z2,z3,z6]),(0,[z29,z0,z1,z54,z2,z6]),(0,[z0,z36,z1,z400,z3,z6]),(1,[z0,z1,z869,z2,z6]),(0,[z0,z1,z11,z3,z431,z6])],[(0,[z1536,z0,z1,z2,z3,z6]),(0,[z0,z1537,z2,z3,z4,z6]),(0,[z0,z1,z1538,z3,z4,z6]),(0,[z1539,z0,z1,z2,z3,z6]),(0,[z1,z2,z3,z4,z6,z1540]),(0,[z28,z0,z377,z2,z3,z6]),(0,[z0,z1,z170,z131,z14,z6]),(0,[z1541,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1542,z6])],[(0,[z420,z1,z2,z3,z24,z6]),(0,[z0,z1543,z2,z3,z4,z6]),(0,[z0,z1,z53,z3,z14,z6]),(0,[z0,z1,z196,z3,z4,z6]),(0,[z0,z1,z2,z3,z1544,z6]),(0,[z0,z1,z2,z43,z3,z6]),(0,[z1128,z0,z1,z196,z3,z6]),(0,[z0,z1,z1413,z3,z4,z6]),(0,[z1,z11,z2,z3,z6,z248]),(0,[z0,z1,z170,z131,z6,z33]),(0,[z0,z1,z2,z3,z6,z230])],[(0,[z80,z41,z2,z3,z120,z6]),(0,[z20,z1,z2,z545,z49,z6]),(0,[z566,z1,z2,z49,z4,z6]),(0,[z568,z0,z2,z3,z16,z6]),(0,[z0,z1,z53,z3,z6,z33]),(0,[z8,z82,z0,z55,z3,z6]),(0,[z0,z1,z2,z3,z1545,z6]),(0,[z0,z1,z2,z3,z78,z163]),(0,[z0,z1,z2,z3,z1546,z6]),(0,[z0,z1547,z1,z2,z3,z6]),(0,[z0,z1,z1548,z2,z3,z6]),(0,[z0,z1,z1549,z2,z3,z6])],[(0,[z0,z1,z2,z3,z6,z1550]),(0,[z0,z1,z2,z3,z1551,z6]),(0,[z8,z0,z1,z53,z3,z6]),(0,[z0,z1,z2,z3,z6,z1552]),(0,[z0,z1,z297,z44,z3,z6]),(0,[z197,z0,z2,z3,z4,z68]),(0,[z17,z0,z1,z170,z131,z6]),(0,[z0,z1,z2,z3,z6,z264]),(0,[z0,z1,z111,z2,z110,z103])],[(0,[z0,z1,z2,z3,z545,z6]),(0,[z0,z1,z2,z3,z1553,z6]),(0,[z1,z2,z3,z6,z248,z805]),(0,[z0,z40,z443,z2,z3,z6]),(0,[z1554,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z544,z6]),(0,[z0,z1,z2,z3,z1555,z6]),(0,[z0,z1,z1556,z2,z3,z6])],[(0,[z0,z1,z1557,z3,z4,z6]),(0,[z0,z1,z2,z1558,z4,z6]),(0,[z0,z1,z2,z3,z1559,z6]),(0,[z0,z2,z255,z3,z129,z6]),(0,[z1560,z0,z1,z2,z3,z6]),(0,[z29,z0,z1,z2,z3,z1040])],[(0,[z0,z1,z2,z3,z1561,z6]),(0,[z0,z1,z2,z3,z1562,z6]),(0,[z0,z114,z2,z3,z1563,z6]),(0,[z0,z1,z1564,z2,z3,z6]),(0,[z0,z1,z1565,z2,z3,z6]),(0,[z0,z1,z2,z3,z335,z6]),(0,[z0,z1,z400,z2,z3,z6]),(0,[z0,z1,z2,z3,z1566,z6]),(0,[z522,z1,z2,z329,z3,z6])]],
   [[(0,[z553,z0,z1,z2,z3,z6]),(0,[z0,z1,z53,z44,z3,z6]),(0,[z25,z1,z2,z44,z3,z185]),(0,[z0,z1,z2,z4,z1567,z6]),(0,[z1568,z0,z1,z2,z3,z6]),(0,[z251,z0,z2,z13,z16,z6]),(0,[z0,z1,z2,z3,z1569,z6]),(0,[z0,z1,z869,z2,z6,z198]),(0,[z0,z1,z2,z3,z1570,z6])],[(0,[z29,z0,z1,z2,z661,z6]),(0,[z0,z1,z1571,z2,z3,z6]),(0,[z556,z0,z1,z63,z3,z6]),(0,[z1572,z0,z1,z2,z3,z6]),(0,[z507,z310,z1,z2,z3,z6]),(0,[z29,z0,z1,z2,z9,z6])],[(0,[z1573,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1574,z6]),(0,[z0,z1,z2,z1575,z3,z6]),(0,[z556,z0,z1,z3,z6,z402]),(0,[z0,z1,z1576,z2,z3,z6]),(0,[z0,z1,z1577,z2,z3,z6]),(0,[z123,z210,z1,z2,z3,z6]),(0,[z0,z1,z79,z2,z3,z6]),(0,[z0,z1,z79,z2,z6,z103]),(0,[z0,z1,z731,z2,z3,z4]),(0,[z225,z1,z2,z3,z6,z368])],[(0,[z0,z51,z2,z303,z3,z6]),(0,[z197,z2,z3,z4,z248,z68]),(0,[z1578,z1,z2,z3,z4,z6])],[(0,[z1579,z0,z1,z2,z3,z6]),(0,[z1580,z0,z1,z2,z3,z6]),(0,[z0,z892,z55,z3,z4,z6]),(0,[z82,z0,z628,z2,z4,z6]),(0,[z0,z1,z100,z2,z43,z6]),(0,[z0,z1,z1581,z2,z3,z6]),(0,[z8,z0,z1,z170,z131,z6]),(0,[z1582,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1583,z6]),(0,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1584,z6]),(0,[z0,z1,z170,z223,z131,z6]),(0,[z0,z1,z2,z3,z1585,z6]),(0,[z8,z0,z924,z2,z3,z6]),(0,[z0,z1,z1586,z2,z3,z6]),(0,[z0,z1,z2,z4,z6,z767])],[(0,[z0,z1,z1587,z3,z4,z6]),(0,[z29,z0,z1,z2,z427,z6]),(0,[z750,z0,z1,z218,z3,z6]),(0,[z0,z1,z53,z179,z4,z6]),(0,[z0,z1,z1507,z2,z3,z6]),(0,[z0,z1,z2,z1061,z26,z6]),(0,[z0,z1,z1588,z2,z3,z6]),(0,[z0,z2,z3,z14,z500,z6]),(0,[z1589,z0,z1,z2,z3,z6]),(0,[z1590,z0,z1,z2,z3,z6]),(0,[z8,z799,z1,z2,z3,z6]),(0,[z0,z1,z245,z2,z3,z33]),(0,[z0,z1,z378,z2,z3,z108]),(0,[z1591,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1592,z6]),(0,[z0,z1,z2,z3,z1593,z6]),(0,[z8,z0,z1,z624,z3,z6]),(0,[z0,z1,z2,z3,z4,z1594]),(0,[z28,z0,z2,z3,z757,z6]),(0,[z0,z406,z2,z3,z14,z6]),(0,[z149,z1,z2,z3,z6,z248]),(0,[z0,z1,z2,z3,z1595,z6]),(0,[z0,z1,z2,z3,z6,z1040]),(0,[z405,z360,z0,z2,z3,z6])]],
   [[(0,[z0,z1,z1346,z2,z3,z4]),(0,[z0,z1,z2,z1278,z4,z6]),(0,[z0,z1,z1596,z3,z4,z6]),(0,[z1597,z0,z1,z2,z3,z6]),(0,[z0,z510,z2,z3,z104,z6]),(0,[z0,z1,z2,z3,z229,z6]),(0,[z0,z1,z170,z131,z16,z6]),(0,[z556,z0,z1,z170,z3,z6]),(0,[z1598,z0,z1,z2,z3,z6]),(0,[z29,z719,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1599,z6]),(0,[z0,z1,z53,z3,z16,z6]),(0,[z0,z1,z2,z3,z1600,z6]),(0,[z1601,z1,z2,z3,z4,z6]),(0,[z1602,z1,z2,z3,z4,z6]),(0,[z1066,z1,z2,z3,z4,z6]),(0,[z1603,z0,z1,z2,z3,z6])],[(0,[z1604,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1605,z6]),(0,[z17,z0,z1,z628,z2,z6]),(0,[z0,z1,z2,z3,z1606,z6]),(0,[z468,z0,z1,z2,z309,z6]),(0,[z0,z236,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z1607,z6]),(0,[z0,z1,z2,z3,z1608,z6]),(0,[z0,z1,z2,z3,z1609,z6])],[(0,[z80,z41,z2,z3,z181,z6]),(0,[z0,z1,z1504,z3,z4,z6]),(0,[z0,z1,z2,z3,z1610,z6]),(0,[z0,z2,z3,z272,z16,z6]),(0,[z25,z1,z2,z3,z104,z185]),(0,[z1611,z0,z1,z2,z3,z6]),(0,[z0,z1,z1612,z2,z3,z6]),(0,[z0,z1,z2,z3,z1613,z6]),(0,[z0,z1,z100,z39,z2,z6]),(0,[z0,z1,z2,z3,z1614,z6]),(0,[z0,z1,z1615,z2,z3,z6])],[(0,[z0,z1,z2,z1616,z3,z6]),(0,[z0,z1,z2,z3,z1617,z6]),(0,[z1618,z0,z1,z2,z3,z6]),(0,[z0,z1,z1619,z2,z4,z6]),(0,[z1620,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z591,z6]),(0,[z1,z997,z2,z3,z4,z6]),(0,[z0,z1,z30,z174,z3,z6])],[(0,[z1621,z0,z1,z2,z3,z6]),(0,[z8,z0,z1,z3,z6,z107])],[(0,[z0,z1,z2,z3,z1622,z6]),(0,[z8,z0,z1,z3,z286,z6]),(0,[z1623,z0,z1,z2,z3,z6])],[(0,[z172,z41,z2,z3,z4,z6]),(0,[z0,z1,z1624,z2,z3,z4]),(0,[z0,z1,z2,z16,z1174,z6]),(0,[z1,z298,z11,z2,z3,z6]),(0,[z0,z1,z2,z3,z1625,z6]),(0,[z0,z1,z135,z2,z3,z171]),(0,[z0,z1,z1626,z2,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z1627,z6]),(0,[z0,z1,z2,z3,z1628,z6]),(0,[z956,z1,z11,z2,z3,z6])],[(0,[z1629,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1630,z6]),(0,[z0,z1,z2,z1631,z3,z6]),(0,[z251,z0,z2,z13,z4,z6])],[(0,[z0,z1,z2,z3,z6,z1632]),(0,[z1,z2,z821,z49,z4,z6]),(0,[z82,z0,z55,z3,z14,z6]),(0,[z8,z0,z1,z628,z2,z6]),(0,[z0,z1,z2,z3,z1633,z6]),(0,[z0,z1634,z1,z2,z3,z6]),(0,[z1635,z0,z1,z2,z3,z6]),(0,[z0,z1,z1636,z2,z3,z6])],[(0,[z29,z0,z114,z2,z3,z6]),(0,[z82,z0,z55,z3,z6,z33]),(0,[z0,z2,z3,z14,z16,z6]),(0,[z0,z1,z2,z3,z1637,z6]),(0,[z0,z40,z2,z3,z221,z6]),(0,[z17,z0,z1,z2,z3,z230]),(0,[z0,z1,z1638,z2,z3,z6])],[(0,[z1639,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1640,z6]),(0,[z1641,z0,z1,z2,z3,z6]),(0,[z168,z0,z158,z2,z3,z6]),(0,[z173,z1,z2,z3,z14,z6]),(0,[z29,z0,z1,z506,z2,z6]),(0,[z0,z1,z1642,z2,z3,z6]),(0,[z0,z1,z2,z3,z12,z6])],[(0,[z0,z1,z2,z3,z1643,z6]),(0,[z0,z1,z2,z3,z6,z1644]),(0,[z0,z1,z2,z3,z1645,z6]),(0,[z0,z1,z2,z3,z1646,z6]),(0,[z17,z0,z1,z2,z26,z6]),(0,[z1647,z0,z1,z2,z3,z6]),(0,[z0,z1,z54,z2,z960,z6]),(0,[z172,z1,z2,z3,z14,z6]),(0,[z0,z409,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z1648,z6]),(0,[z0,z1,z46,z3,z6,z107])],[(0,[z0,z1,z2,z3,z1649,z6]),(0,[z0,z1,z2,z3,z1650,z6]),(0,[z172,z1,z2,z3,z6,z33]),(0,[z1415,z0,z1,z2,z3,z6]),(0,[z0,z1,z39,z2,z3,z6]),(0,[z0,z1,z2,z1651,z3,z6])],[(0,[z0,z1,z2,z1652,z3,z6]),(0,[z0,z1,z2,z1653,z4,z6]),(0,[z17,z0,z1,z218,z3,z6]),(0,[z1654,z0,z1,z2,z3,z6]),(0,[z1655,z0,z1,z2,z3,z6])]],
   [[(0,[z25,z1,z2,z3,z4,z470]),(0,[z8,z0,z1,z609,z3,z6]),(0,[z0,z1,z1656,z3,z4,z6]),(0,[z0,z1657,z2,z3,z4,z6]),(0,[z988,z0,z1,z53,z3,z6]),(0,[z1,z2,z3,z4,z1450,z185]),(0,[z82,z0,z55,z44,z3,z6]),(0,[z1658,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1659,z6]),(0,[z0,z377,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z1660,z6]),(0,[z1661,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z1662,z4,z6]),(0,[z0,z1,z1663,z2,z3,z4]),(0,[z8,z20,z1,z2,z49,z6]),(0,[z838,z0,z1,z2,z26,z6]),(0,[z0,z1,z170,z131,z4,z6]),(0,[z8,z0,z1,z364,z3,z6]),(0,[z1,z997,z11,z2,z3,z6]),(0,[z1,z2,z3,z6,z33,z877])],[(0,[z0,z1,z53,z3,z4,z6]),(0,[z0,z1,z2,z3,z1664,z6]),(0,[z17,z0,z1,z54,z2,z6]),(0,[z29,z0,z1,z2,z363,z6]),(0,[z0,z1,z2,z3,z1665,z6])],[(0,[z0,z1,z1666,z3,z4,z6]),(0,[z0,z1,z1667,z2,z3,z6]),(0,[z0,z1,z2,z3,z1668,z6]),(0,[z23,z1,z2,z3,z857,z6]),(0,[z1669,z0,z1,z2,z3,z6]),(0,[z172,z1,z2,z44,z3,z6]),(0,[z360,z0,z30,z3,z4,z6]),(0,[z0,z1,z2,z3,z1670,z6]),(0,[z0,z1,z63,z3,z367,z136])],[(0,[z0,z1,z1671,z2,z4,z6]),(0,[z0,z1,z2,z3,z1672,z6]),(0,[z0,z628,z51,z2,z4,z6]),(0,[z0,z1,z2,z3,z1673,z6]),(0,[z0,z1,z2,z14,z6,z1074]),(0,[z0,z1,z90,z39,z2,z6]),(0,[z0,z1,z2,z3,z1674,z6]),(0,[z0,z1,z1675,z2,z3,z6])],[(0,[z8,z0,z1,z692,z3,z6]),(0,[z0,z1,z1676,z2,z3,z6]),(0,[z0,z1,z2,z1677,z3,z6]),(0,[z0,z1,z74,z2,z3,z6]),(0,[z0,z1,z2,z3,z1678,z6]),(0,[z0,z1,z63,z3,z212,z136]),(0,[z0,z1,z1679,z2,z3,z6]),(0,[z0,z1,z48,z2,z3,z175]),(0,[z0,z1,z1680,z2,z3,z6])],[(0,[z1681,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1682,z6]),(0,[z0,z1,z2,z3,z223,z6])],[(0,[z80,z510,z2,z3,z4,z6]),(0,[z0,z1,z1683,z2,z3,z4]),(0,[z0,z1,z2,z1684,z4,z6]),(0,[z8,z0,z1,z218,z3,z6]),(0,[z0,z1685,z1,z2,z3,z6]),(0,[z251,z0,z2,z229,z13,z6]),(0,[z0,z1,z1686,z2,z3,z6]),(0,[z0,z1,z1687,z2,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z6,z1688]),(0,[z0,z1,z2,z1689,z3,z6]),(0,[z0,z1,z2,z3,z1690,z6]),(0,[z0,z1,z2,z1691,z3,z6]),(0,[z0,z36,z51,z3,z16,z6]),(0,[z0,z1,z2,z3,z6,z1692]),(0,[z0,z1,z2,z1693,z3,z6]),(0,[z1694,z0,z1,z2,z3,z6]),(0,[z0,z1,z1695,z2,z3,z6])],[(0,[z277,z0,z2,z3,z16,z6]),(0,[z82,z0,z55,z3,z16,z6]),(0,[z197,z0,z2,z3,z68,z198]),(0,[z0,z1,z2,z3,z6,z1696])],[(0,[z0,z1,z2,z3,z1697,z6]),(0,[z1698,z0,z1,z2,z3,z6]),(0,[z1699,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1700,z6]),(0,[z0,z1,z2,z3,z4,z767])],[(0,[z0,z1,z2,z3,z1563,z6]),(0,[z0,z1,z2,z1701,z3,z6]),(0,[z173,z1,z2,z3,z16,z6]),(0,[z29,z0,z1,z2,z43,z6]),(0,[z1702,z0,z1,z2,z3,z6]),(0,[z1703,z0,z1,z2,z3,z6]),(0,[z0,z1,z1704,z2,z3,z6])],[(0,[z0,z1,z2,z3,z6,z146]),(0,[z0,z510,z11,z2,z3,z6]),(0,[z0,z1,z2,z3,z1705,z6]),(0,[z251,z0,z2,z13,z62,z6]),(0,[z172,z1,z2,z3,z16,z6]),(0,[z29,z197,z0,z2,z3,z68]),(0,[z0,z1,z2,z3,z1706,z6])],[(0,[z1707,z0,z1,z2,z3,z6]),(0,[z0,z1,z628,z2,z14,z6]),(0,[z0,z1,z2,z3,z1363,z6]),(0,[z0,z158,z2,z55,z3,z6]),(0,[z197,z0,z2,z44,z3,z68]),(0,[z0,z1,z2,z3,z6,z1708])],[(0,[z0,z1,z2,z3,z1709,z6]),(0,[z0,z1,z2,z3,z1710,z6]),(0,[z0,z1,z628,z2,z6,z33]),(0,[z0,z1,z2,z3,z1711,z6]),(0,[z0,z2,z3,z244,z14,z6]),(0,[z0,z1,z30,z234,z3,z6]),(0,[z1712,z0,z1,z2,z3,z6]),(0,[z0,z1,z608,z11,z3,z6]),(0,[z0,z1,z2,z3,z6,z1713])],[(0,[z0,z1,z2,z1714,z4,z6]),(0,[z17,z80,z41,z2,z3,z6]),(0,[z0,z1,z2,z3,z801,z6]),(0,[z25,z1,z11,z2,z3,z185]),(0,[z0,z1,z2,z3,z1715,z6]),(0,[z0,z1,z2,z3,z6,z1716]),(0,[z28,z0,z2,z3,z16,z6]),(0,[z172,z1,z2,z3,z1217,z6]),(0,[z0,z1,z2,z3,z6,z1717]),(0,[z29,z0,z1,z2,z3,z849])]],
   [[(0,[z0,z510,z2,z3,z50,z6]),(0,[z1718,z0,z1,z2,z3,z6]),(0,[z1719,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z129,z6]),(0,[z0,z1,z746,z3,z16,z6]),(0,[z0,z1,z2,z16,z1567,z6]),(0,[z0,z2,z3,z14,z578,z6]),(0,[z0,z1,z2,z3,z1720,z6]),(0,[z8,z0,z1,z2,z3,z1040]),(0,[z0,z1,z111,z2,z33,z103])],[(0,[z29,z0,z1,z2,z3,z6]),(0,[z1721,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z1722,z4,z6]),(0,[z0,z1,z2,z3,z6,z1723]),(0,[z0,z1,z400,z11,z3,z6]),(0,[z0,z1,z63,z3,z4,z759])],[(0,[z0,z1,z2,z3,z1724,z6]),(0,[z0,z1,z2,z3,z1725,z6]),(0,[z0,z1726,z1,z2,z3,z6]),(0,[z251,z0,z651,z2,z4,z6]),(0,[z556,z0,z1,z11,z3,z6]),(0,[z0,z1,z2,z4,z1174,z6]),(0,[z0,z1,z763,z3,z6,z68]),(0,[z719,z1,z2,z3,z4,z6]),(0,[z1727,z1,z2,z3,z4,z6])],[(0,[z0,z1,z1728,z2,z4,z6]),(0,[z0,z1,z2,z1145,z4,z6]),(0,[z25,z1,z2,z3,z50,z185]),(0,[z0,z1,z2,z1729,z3,z6]),(0,[z0,z1,z2,z760,z16,z6]),(0,[z0,z1,z2,z3,z6,z1730]),(0,[z0,z1,z2,z3,z6,z1731]),(0,[z17,z0,z1,z2,z3,z93]),(0,[z0,z1,z2,z3,z1732,z6])],[(0,[z0,z1,z2,z3,z1733,z6]),(0,[z8,z0,z1,z425,z3,z6]),(0,[z0,z1,z1588,z196,z3,z6]),(0,[z0,z1,z2,z3,z1734,z6])],[(0,[z29,z133,z1,z42,z3,z6]),(0,[z1735,z0,z1,z2,z3,z6]),(0,[z1,z2,z3,z4,z857,z6]),(0,[z1736,z1,z2,z3,z4,z6]),(0,[z1737,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1738,z6]),(0,[z0,z1,z2,z3,z1161,z6]),(0,[z0,z1,z1739,z2,z3,z6]),(0,[z0,z1,z63,z3,z544,z136])],[(0,[z20,z1,z2,z49,z14,z6]),(0,[z0,z1,z2,z3,z1740,z6]),(0,[z1084,z0,z1,z2,z179,z6]),(0,[z29,z0,z1,z2,z6,z295]),(0,[z0,z1,z79,z48,z2,z6])],[(0,[z0,z1,z2,z1741,z4,z6]),(0,[z1742,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1743,z6]),(0,[z0,z1,z46,z190,z3,z6]),(0,[z0,z1,z2,z3,z1744,z6]),(0,[z0,z1,z158,z2,z3,z6]),(0,[z0,z1,z2,z3,z1745,z6]),(0,[z360,z0,z11,z2,z3,z6]),(0,[z0,z1,z63,z3,z33,z136])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 460).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 920).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1380).take 272) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1652)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [460, 460, 460, 272] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 64).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 64).take 68).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 132).take 67).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 199).take 57).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [64, 68, 67, 57] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

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

end PEqualNP.Outside.L_meta_45938

theorem PEqualNP.Outside.L_meta_45938 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677312 * 2 ^ 32 + 4276660864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677312 * 2 ^ 32 + 4276660864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_45938.solve