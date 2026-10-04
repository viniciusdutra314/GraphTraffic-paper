# Roteamento por visibilidade limitada — Lean 4

**O teorema final usa somente um grafo finito, simples, não direcionado e conexo,
a origem, o destino e um raio natural.** Absorção quase certa, primeiro e segundo
momentos finitos e invertibilidade de `I − Q` são demonstrados.

## Compilar

```bash
cd Proofs
nix develop --command lake build
nix develop --command lake env lean Audit.lean
```

Também funciona `nix develop`, seguido de `lake build`. Se flakes não estiverem
habilitados, use `nix --extra-experimental-features 'nix-command flakes' develop`.
O primeiro uso requer rede; `lake exe cache get`, dentro do shell, permite usar
o cache do mathlib. Os arquivos do flake precisam ser conhecidos pelo Git.

Versões fixadas:

- Lean/Lake **4.19.0**, por `lean-toolchain`;
- mathlib **v4.19.0**, revisão `c44e0c8ee63ca166450922a373c7409c5d26b00b`;
- nixpkgs `ac62194c3917d5f474c1a844b6fd6da2db95077d`, com hash em `flake.lock`;
- dependências transitivas fixadas por `lake-manifest.json`.

O flake fornece elan 4.1.1, Git e ferramentas de download/compilação. O elan do
Nix adapta o toolchain ao runtime Nix; não há dependência de Lean global.
Entre no shell em `Proofs/`: toolchain e cache ficam em `.elan` e `.cache/mathlib`.
A plataforma efetivamente testada é x86_64-linux. Veja `VALIDATION.md`.

## O enunciado

A caminhada escolhe uniformemente um vizinho enquanto `d(v,t) > r`. Ao entrar
na bola visível, segue um caminho mínimo até `t`.

- `Outside G t r = {v // r < G.dist v t}` é o tipo dos estados transientes.
- `transition G t r` é **Q**, a matriz restrita aos estados transientes,
  com entrada `1 / degree(i)` para vizinhos e zero caso contrário.
- **N = (I − Q)⁻¹**, `meanVector N = N 1` e `secondVector N = (2N − I)N1`.
- `expectedRoute` e `routeVariance` usam a integral e a variância do mathlib.

Em `Main.lean`, com os parâmetros de seção
`[Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]`:

```lean
theorem route_statistics (hG : G.Connected) (t : V) (r : ℕ)
    (s : V) :
    let N := (1 - transition G t r)⁻¹
    (expectedRoute G hG t r s =
      if hs : r < G.dist s t then (r : ℝ) + meanVector N ⟨s, hs⟩ else (G.dist s t : ℝ)) ∧
    (routeVariance G hG t r s =
      if hs : r < G.dist s t then secondVector N ⟨s, hs⟩ - (meanVector N ⟨s, hs⟩) ^ 2 else 0)
```

As instâncias de decidibilidade servem à representação das somas e matrizes;
não acrescentam restrições na matemática clássica. O tipo transiente pode ser
vazio. Nenhuma hipótese de absorção, de momentos ou de inversa é fornecida pelo
usuário, nem mesmo às definições de esperança e variância da rota.

## A demonstração para leitura humana

**1. Geometria.** Uma aresta altera a distância ao destino em no máximo um.
Logo, uma entrada na bola a partir de fora termina na esfera `d(v,t) = r`.
Portanto `L = T + r`. Se a origem já está visível, `T = 0` e `L = d(s,t)`.
`FirstHit` descreve exatamente um prefixo adjacente que permanece fora antes
do primeiro tempo de entrada. Um caminho mínimo realiza o sufixo determinístico.

**2. Comparação pelo Laplaciano do mathlib.** Estenda o vetor transiente `x`
por zero na bola, obtendo `f`, e tome `g(v) = min(f(v), 0)`. Denote por `Δ`
o Laplaciano do grafo. Se `(I − Q)x ≥ 0`, então `Δf(v) ≥ 0` fora da bola.
Quando `f(v) < 0`, temos `g(v) = f(v)` e `g(w) ≤ f(w)` para os vizinhos;
logo `Δg(v) ≥ Δf(v) ≥ 0`. Quando `f(v) ≥ 0`, temos `g(v) = 0`. Portanto
cada parcela de `gᵀΔg` é não positiva.

O mathlib fornece os dois fatos que encerram o argumento: `Δ` é positivo
semidefinido, e energia zero implica constância em cada componente conexa.
Assim `gᵀΔg = 0`, `g` é constante e, como `g(t) = 0`, `g = 0`. Concluímos

```text
(I − Q)x ≥ 0  ⇒  x ≥ 0.
```

Aplicando isso a `x` e `−x`, o núcleo de `I − Q` é trivial. O critério padrão
`Matrix.mulVec_injective_iff_isUnit` dá a invertibilidade. Para resolver os
sistemas dos momentos, usamos `Matrix.inv_mulVec_eq_vec`; a estrutura própria
`Fundamental` e seu lema de resolução foram removidos.

**3. Um único lema de somabilidade.** Para vetores não negativos que satisfaçam
`a₀ = 0` e `aₙ₊₁ = bₙ + Q aₙ`, suponha que a soma de `bₙ` seja finita. Escreva
`Sₙ = sum_{k<n} aₖ`, `Bₙ = sum_{k<n} bₖ` e `B = sum_k bₖ`. Telescopando:

```text
(I − Q)Sₙ = Bₙ − aₙ ≤ B = (I − Q)NB.
```

O princípio do mínimo implica `0 ≤ Sₙ ≤ NB`. As somas parciais crescem e são
limitadas; portanto `sum aₙ` é finita. Esse é `summable_recurrence`.

**4. Absorção e momentos.** A massa de primeiro hitting é definida por

```text
p₀ = 0,
pₙ₊₁ = 1_{n=0}(1 − Q1) + Qpₙ.
```

Ela é não negativa pela substocasticidade. Aplicamos o lema anterior três vezes:

| Saída `aₙ` | Entrada `bₙ` |
| --- | --- |
| `pₙ` | `1_{n=0}(1 − Q1)` |
| `n pₙ` | `pₙ₊₁` |
| `n² pₙ` | `(2n+1)pₙ₊₁ = 2(n+1)pₙ₊₁ − pₙ₊₁` |

Cada entrada é somável pelo passo anterior. Além disso, `s = sum pₙ` satisfaz
`(I − Q)s = 1 − Q1`, portanto `s = 1` pela invertibilidade. Isso prova absorção
total e os momentos finitos. O teorema `graph_regular` empacota esses resultados
em `HittingRegular`; essa estrutura agora é uma **conclusão demonstrada**.
Não é necessário construir uma estimativa de cauda geométrica.

**5. Fórmulas.** Somando a análise do primeiro passo:

```text
m = 1 + Qm,             z = 1 + 2Qm + Qz.
m = N1,                 z = N(1 + 2Qm) = (2N − I)N1.
```

A solução é única. A variância é `z_s − m_s²`; adicionar `r` à variável não a
altera. O caso visível é constante e tem variância zero.

## Onde conferir cada passo

| Leitura | Arquivos em `LimitedVisibility/` |
| --- | --- |
| Enunciado final e os dois casos | `Main.lean`, `RouteLength.lean` |
| Passo 1 | `GraphGeometry.lean` |
| Definição de Q e substocasticidade | `TransitionMatrix.lean` |
| Passo 2 | `MaximumPrinciple.lean` |
| Passos 3 e 4 | `Summability.lean`, `Absorption.lean` |
| Lei de primeiro hitting e recorrências | `HittingTime.lean` |
| Álgebra do passo 5 | `FundamentalMatrix.lean`, `FirstMoment.lean`, `SecondMoment.lean` |
| Integrais, variância e translação | `DiscreteProbability.lean`, `Variance.lean` |
| Exemplos: uma aresta e região totalmente visível | `Examples.lean` |

A formalização usa a lei discreta de hitting construída por probabilidades
finitas, convertida em `PMF ℕ`. Não constrói um processo em um espaço de
trajetórias infinitas: a ligação geométrica é provada para todo certificado
`FirstHit`, e a lei é dada pela recorrência de primeiro passo acima.

## Resultados de biblioteca reutilizados

| Etapa | Resultado do mathlib |
| --- | --- |
| Comparação | `SimpleGraph.posSemidef_lapMatrix` e `lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable` |
| Núcleo trivial e invertibilidade | `injective_iff_map_eq_zero`, `Matrix.mulVec_injective_iff_isUnit` |
| Identidade da inversa e solução linear | `Matrix.mul_nonsing_inv`, `Matrix.inv_mulVec_eq_vec` |
| Partição entre estados visíveis e transientes | `Fintype.sum_subtype_add_sum_subtype`, `Equiv.subtypeEquivRight`, `Equiv.sum_comp` |
| Convergência e soma do primeiro passo | `summable_of_sum_range_le`, `hasSum_sum`, `hasSum_nat_add_iff'` |
| Esperança e variância | `PMF.integral_eq_tsum`, `ProbabilityTheory.variance_def'` |

As versões efetivamente importadas são as do mathlib fixado no projeto:
[Laplaciano](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/SimpleGraph/LapMatrix.lean)
e [inversa de matrizes](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean).

Também foi consultado o projeto externo
[trace-logic-lean](https://github.com/velvetmonkey/trace-logic-lean/blob/main/RequestProject/TraceLogicPhase5.lean).
Seu resultado de invertibilidade exige que alguma potência da matriz tenha
todas as somas de linha estritamente menores que um. Essa condição não é
imediata da nossa representação: seria necessário provar a estimativa de
escape. Ele usa mathlib 4.28.0. Não foi incorporado como dependência, pois não
elimina a parte específica do grafo. Na pesquisa realizada, não foi encontrado
um teorema pronto que entregasse absorção e os dois momentos diretamente a
partir dos parâmetros deste problema.

O trabalho próprio restante liga a transição uniforme ao Laplaciano, prova
o lema da recorrência com entrada somável e aplica esse lema à lei de hitting.
A conectividade e a finitude continuam suficientes; não adicionamos hipóteses
analíticas para usar uma biblioteca.

## Auditoria

`lake build` verifica todos os módulos e exemplos. `Audit.lean` inspeciona os
teoremas principais, incluindo a nova prova de absorção. Os únicos fundamentos
listados são `propext`, `Classical.choice` e `Quot.sound`.
Não há `sorry`, `admit`, axiomas personalizados ou uso de `native_decide` nos
fontes próprios. Não resta hipótese analítica pendente no teorema final.
