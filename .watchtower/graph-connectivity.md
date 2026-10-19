# Conectividade de grafos com mínima perturbação

## Checklist — Vinícius
- [ ] Conferir a versão local de `__connect_graph!` e corrigir a elegibilidade dos *edge swaps*: uma única componente com aresta não-ponte é suficiente, desde que a outra tenha uma aresta.
- [ ] Buscar pares elegíveis antes de recorrer à adição de arestas; não tomar o fracasso de um par sorteado como impossibilidade global.
- [ ] Manter sorteios entre alternativas elegíveis, a interface mutante e a implementação simples em Graphs.jl; integrar a correção ao GraphTraffic.

## Checklist — Chloe
- [ ] Preparar o teste de regressão **triângulo + aresta isolada**, verificando conectividade, número de arestas e graus por vértice.
- [ ] Confirmar que o teste distingue a implementação original da corrigida.
- [ ] Revisar a solução resultante contra os invariantes e decisões desta spec, sem exigir a mesma estrutura interna.

## Checklist — A definir
- [ ] Definir responsável pelos testes complementares de árvores, múltiplas componentes, isolados e sementes aleatórias.
- [ ] Decidir a política para vértices isolados e agrupamento de componentes sem arestas.
- [ ] Definir, se necessário para o artigo, uma medida quantitativa de perturbação topológica e suas métricas de validação.

## Objetivo e motivação

O GraphTraffic usa grafos que precisam ser conexos para os experimentos de tráfego. Quando um gerador produz um grafo desconexo, queremos **reparar aquele grafo específico**, não construir outro grafo qualquer que satisfaça algumas estatísticas. Mudanças artificiais de conectividade podem afetar caminhos, graus, concentração de fluxo e a comparabilidade entre topologias.

A prioridade operacional é aproveitar alterações que preservem o número de arestas e os graus individuais, evitando adições desnecessárias. Isso **não equivale** a uma definição demonstrada de “mínima perturbação topológica”: preservar graus não preserva necessariamente clustering, distâncias, betweenness ou resultados de tráfego.

## Decisões e justificativas

1. **Corrigir a condição de troca.** A implementação original examinada escolhe duas componentes ao acaso e só faz um *double-edge swap* quando encontra arestas não-pontes nas duas. Isso é restritivo demais. Se `A` possui uma aresta não-ponte `(u,v)` e `B` possui qualquer aresta `(x,y)`, podemos remover ambas e inserir `(u,x)` e `(v,y)`. A remoção em `A` não a desconecta; mesmo que `(x,y)` seja ponte, os dois lados de `B` ficam ligados a `A`. O número total de arestas e o grau de cada vértice permanecem iguais, e as duas componentes tornam-se uma.
2. **Procurar uma troca viável antes de adicionar.** Um par sorteado pode ser inelegível enquanto outro permitir a troca. A escolha aleatória deve ocorrer entre alternativas viáveis, não justificar uma adição prematura. Cada operação precisa reduzir o número de componentes.
3. **Preservar aleatoriedade sem prometer amostragem uniforme.** Evitar uma ordem determinística que privilegie vértices/componentes por índice. Não foi estabelecida distribuição uniforme sobre todos os grafos resultantes ou sobre todas as operações possíveis.
4. **Preferir simplicidade à otimização prematura.** Recalcular componentes e pontes depois de cada alteração é aceitável para a escala prevista (aproximadamente quatro topologias). Não introduzir arquitetura, caches ou dependências extras sem necessidade.
5. **Reconhecer limites matemáticos.** Duas árvores não podem ser unidas por essa troca sem manter a desconexão; uma floresta exige adições. Vértices isolados têm grau zero, portanto não podem ingressar em um grafo conexo preservando seus graus. O caso de isolados precisa de política própria.

A literatura de Viger–Latapy e Horvát–Modes trata de construção/amostragem de grafos conexos com sequência de graus prescrita. É relacionada, mas não resolve diretamente o problema de modificar minimamente a topologia **de um grafo de entrada determinado**. Não transformar essa distinção em alegação de optimalidade do nosso método.

## Comportamento esperado

**Interface existente:** `__connect_graph!(g::Graphs.SimpleGraph)`, mutando o grafo recebido e retornando `g`. Nenhuma nova assinatura ou estrutura obrigatória foi decidida.

- Entrada: grafo simples, não direcionado, possivelmente desconexo. Preservar o conjunto de vértices.
- Se já for conexo, não modificá-lo.
- Enquanto houver mais de uma componente, identificar pares elegíveis: uma componente com pelo menos uma aresta não-ponte e outra com pelo menos uma aresta (que pode ser ponte).
- Havendo pares elegíveis, escolher aleatoriamente componentes/arestas compatíveis, executar a troca cruzada e recalcular o estado.
- Não havendo troca elegível, conectar duas componentes por uma adição de aresta; recalcular o estado. O tratamento preciso dos isolados permanece aberto.
- Ao terminar, entregar um grafo conexo e simples, sem laços nem arestas paralelas. Em cada troca, conservar `ne(g)` e o grau individual dos vértices; adições podem alterar esses valores.

A spec fixa **propriedades e intenção**, não uma sequência literal de chamadas de Graphs.jl. Uma implementação diferente é aceitável se cumprir os invariantes e justificar melhorias.

## Verificação

**Regressão obrigatória:** `V = {1,2,3,4,5}` e `E = {(1,2),(2,3),(1,3),(4,5)}`. O triângulo mais a componente de dois vértices deve tornar-se conexo **sem aumentar as quatro arestas** e mantendo os graus `[2,2,2,1,1]` por vértice. Uma transformação válida remove `(1,2)` e `(4,5)` e adiciona `(1,4)` e `(2,5)`. A regra antiga adicionaria uma aresta, embora a troca seja possível.

Testes complementares a atribuir: duas componentes cíclicas; uma cíclica com várias árvores; pares inelegíveis na presença de um terceiro componente elegível; floresta sem ciclos; isolados; grafo já conexo; diferentes sementes aleatórias. Verificar `nv`, conectividade, simplicidade e grau/arestas conforme o tipo de operação. Conferir separadamente se a criação dos grafos de entrada preserva os vértices isolados.

**Aceitação da correção local:** a regressão passa, nenhuma adição ocorre enquanto há uma troca elegível segundo a política acordada, todas as operações progridem rumo à conectividade, e a implementação permanece simples e verificável. Não é necessário solucionar o problema geral de otimização topológica nesta etapa. Nenhum teste ou alteração na versão de trabalho está confirmado por esta spec.

## Questões abertas

- Qual métrica deve representar a perturbação topológica: graus, quantidade/conjunto de arestas, clustering, distâncias, betweenness, estrutura espacial ou impacto nas simulações? Como conciliar critérios conflitantes?
- Como tratar vários vértices isolados para evitar adições globais desnecessárias? Agrupá-los primeiro pode ajudar, mas não foi adotado como regra.
- A estratégia aleatória introduz vieses relevantes? Vale comparar distribuições ou exigir reprodutibilidade controlada?
- Quais garantias globais sobre número mínimo de adições podem ser demonstradas, dadas as operações permitidas?
- Há necessidade de critérios espaciais específicos para a topologia Random Geometric, evitando atalhos artificiais?

## Referências de trabalho

- [Implementação original examinada — `undergraduate-thesis/src/GraphTraffic.jl`](https://github.com/viniciusdutra314/undergraduate-thesis/blob/main/src/GraphTraffic.jl) — referência histórica; conferir a versão local antes de editar.
- [Graphs.jl — documentação](https://juliagraphs.org/Graphs.jl/stable/).
- [Viger & Latapy, *Fast generation of random connected graphs with prescribed degrees* (2005)](https://arxiv.org/abs/cs/0502085).
- [Horvát & Modes, *Connectedness matters: Construction and exact random sampling of connected graphs*](https://arxiv.org/abs/2009.03747) (versão arXiv; título publicado usa “networks”).
