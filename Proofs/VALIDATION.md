# Validação da simplificação com resultados do mathlib

Revisão verificada em 3 de outubro de 2026, em x86_64-linux.

## Compilação

Em `Proofs/`, foi executado:

```bash
/nix/var/nix/profiles/default/bin/nix \
  --extra-experimental-features 'nix-command flakes' \
  develop --command lake build
```

Código de saída **0**, sem erros ou avisos do Lean:

```text
Build completed successfully.
```

As flags habilitam flakes neste ambiente. Com esse suporte já configurado,
o comando equivalente é `nix develop --command lake build`.
O aviso do Nix sobre alterações locais no checkout Git é esperado.

Lean/Lake permanecem em **4.19.0** e mathlib na revisão
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. Não houve troca de toolchain.
O build usou as dependências já baixadas; não se afirma um novo teste em uma
máquina vazia, nem testes em Darwin ou aarch64.

## Auditoria lógica

Foi executado `lake env lean Audit.lean`, com o Lake do toolchain local
fornecido pelo Nix. Código de saída **0**. Todos os teoremas auditados listaram
somente os fundamentos usuais:

```text
[propext, Classical.choice, Quot.sound]
```

A auditoria inclui `minimum_principle`, `graph_regular`, `transition_det_isUnit`,
`summable_recurrence`, `route_statistics`, a geometria, os momentos,
a fórmula da variância e o exemplo de dois vértices.

Uma busca em todos os **17 arquivos Lean próprios** encontrou zero ocorrências
de `sorry`, `admit`, declarações `axiom` e `native_decide`. Dependências e arquivos
gerados em `.lake` e `.elan` foram excluídos. Nenhum axioma personalizado foi
usado para contornar uma prova.

## Escopo efetivamente provado

- `graph_regular` demonstra absorção total e segundo momento finito somente
a partir da finitude e conectividade do grafo.
- `transition_det_isUnit` demonstra invertibilidade independentemente dos momentos.
- `route_statistics`, `expectedRoute` e `routeVariance` não recebem argumento
`HittingRegular` nem hipótese analítica equivalente.
- O alvo padrão verifica também o exemplo de uma única aresta, com esperança
um e variância zero, e o caso em que toda a região já é visível.
- Não há hipótese de absorção ou momento finito pendente no resultado final.

A nova demonstração usa o princípio do mínimo e somas parciais limitadas;
ela não depende de uma estimativa de cauda geométrica.

## Simplificação com bibliotecas

Comparação com a versão imediatamente anterior, que já era incondicional:

| Fontes | Antes | Depois |
| --- | ---: | ---: |
| Todos os 14 módulos em `LimitedVisibility/` | 895 | 842 |
| `FundamentalMatrix`, `FirstMoment`, `SecondMoment` | 95 | 75 |
| `HittingTime` | 128 | 111 |

Contagem de linhas físicas, incluindo comentários e linhas vazias, nos mesmos
arquivos. A redução total é de **53 linhas (5,9%)**. Não inclui README, auditoria
ou dependências; não houve transferência de código próprio para outro arquivo.

- O princípio do mínimo aplica a positividade e a caracterização de energia
zero do Laplaciano fornecidas pelo mathlib. A construção manual do mínimo e
a indução sobre caminhos foram eliminadas.
- A estrutura própria `Fundamental`, seu lema de resolução e a identidade
auxiliar `Q_mul_N` foram removidos. Os momentos usam a inversa canônica e
`Matrix.inv_mulVec_eq_vec`. O critério de invertibilidade é o do mathlib.
- A troca entre subtipos usa `Equiv.subtypeEquivRight` e `Equiv.sum_comp`,
eliminando uma equivalência construída campo por campo.
- As somas do primeiro passo usam diretamente a distributividade e
`hasSum_sum`, sem provas pontuais adicionais de associatividade.

O README explica o argumento atualizado e identifica os resultados importados.
A pesquisa incluiu a documentação atual do mathlib e `trace-logic-lean`; o
segundo exige uma condição de escape em alguma potência da matriz e não foi
adicionado como dependência. Lean, mathlib e os arquivos de lock permanecem
nas mesmas versões. Não se afirma que toda a teoria de cadeias absorventes
esteja pronta nas bibliotecas consultadas.

As alterações de arquivos do repositório estão restritas a `Proofs/`.
