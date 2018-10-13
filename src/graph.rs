use std::mem;
use std::ops::Index;

use petgraph::algo::is_cyclic_directed;
use petgraph::prelude::{DiGraph, Direction, EdgeRef, Graph, NodeIndex};

use error::DepGraphError;
use petgraph::graph::node_index;
use std::fmt;
use Features;
use std::marker::PhantomData;

/// A builder for `Token`s.
///
/// The `Token` type stores a CoNLL-X token. However, since this format
/// permits a large number of fields, construction of a token can get
/// tedious. This builder provides a fluent interface for creating `Token`s.
pub struct TokenBuilder {
    token: Token,
}

impl TokenBuilder {
    /// Create a `Token` builder with all non-form fields set to absent.
    pub fn new<S>(form: S) -> TokenBuilder
    where
        S: Into<String>,
    {
        TokenBuilder {
            token: Token::new(form),
        }
    }

    /// Set the word form or punctuation symbol.
    pub fn form<S>(mut self, form: S) -> TokenBuilder
    where
        S: Into<String>,
    {
        self.token.set_form(form);
        self
    }

    /// Set the lemma or stem of the word form.
    pub fn lemma<S>(mut self, lemma: S) -> TokenBuilder
    where
        S: Into<String>,
    {
        self.token.set_lemma(Some(lemma));
        self
    }

    /// Set the coarse-grained part-of-speech tag.
    pub fn cpos<S>(mut self, cpos: S) -> TokenBuilder
    where
        S: Into<String>,
    {
        self.token.set_cpos(Some(cpos));
        self
    }

    /// Set the fine-grained part-of-speech tag.
    pub fn pos<S>(mut self, pos: S) -> TokenBuilder
    where
        S: Into<String>,
    {
        self.token.set_pos(Some(pos));
        self
    }

    /// Set the syntactic and/or morphological features of the token.
    pub fn features(mut self, features: Features) -> TokenBuilder {
        self.token.set_features(Some(features));
        self
    }
}

impl From<Token> for TokenBuilder {
    fn from(token: Token) -> Self {
        TokenBuilder { token }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Token {
    form: String,
    lemma: Option<String>,
    cpos: Option<String>,
    pos: Option<String>,
    features: Option<Features>,
    secondary_edge: Option<String>,
    secondary_head: Option<usize>,
}

impl Token {
    /// Create a new token where all the non-form fields are absent.
    pub fn new<S>(form: S) -> Token
    where
        S: Into<String>,
    {
        Token {
            form: form.into(),
            lemma: None,
            cpos: None,
            pos: None,
            features: None,
            secondary_edge: None,
            secondary_head: None,
        }
    }

    /// Get the word form or punctuation symbol.
    pub fn form(&self) -> &str {
        self.form.as_ref()
    }

    /// Get the lemma or stem of the word form.
    pub fn lemma(&self) -> Option<&str> {
        self.lemma.as_ref().map(String::as_ref)
    }

    /// Get the coarse-grained part-of-speech tag.
    pub fn cpos(&self) -> Option<&str> {
        self.cpos.as_ref().map(String::as_ref)
    }

    /// Get the fine-grained part-of-speech tag.
    pub fn pos(&self) -> Option<&str> {
        self.pos.as_ref().map(String::as_ref)
    }

    /// Get the syntactic and/or morphological features of the token.
    pub fn features(&self) -> Option<&Features> {
        self.features.as_ref()
    }

    /// Set the word form or punctuation symbol.
    ///
    /// Returns the form that is replaced.
    pub fn set_form<S>(&mut self, form: S) -> String
    where
        S: Into<String>,
    {
        mem::replace(&mut self.form, form.into())
    }

    /// Set the lemma or stem of the word form.
    ///
    /// Returns the lemma that is replaced.
    pub fn set_lemma<S>(&mut self, lemma: Option<S>) -> Option<String>
    where
        S: Into<String>,
    {
        mem::replace(&mut self.lemma, lemma.map(|i| i.into()))
    }

    /// Set the coarse-grained part-of-speech tag.
    ///
    /// Returns the coarse-grained part-of-speech tag that is replaced.
    pub fn set_cpos<S>(&mut self, cpos: Option<S>) -> Option<String>
    where
        S: Into<String>,
    {
        mem::replace(&mut self.cpos, cpos.map(|i| i.into()))
    }

    /// Set the fine-grained part-of-speech tag.
    ///
    /// Returns the fine-grained part-of-speech tag that is replaced.
    pub fn set_pos<S>(&mut self, pos: Option<S>) -> Option<String>
    where
        S: Into<String>,
    {
        mem::replace(&mut self.pos, pos.map(|i| i.into()))
    }

    /// Set the syntactic and/or morphological features of the token.
    ///
    /// Returns the features that are replaced.
    pub fn set_features(&mut self, features: Option<Features>) -> Option<Features> {
        mem::replace(&mut self.features, features)
    }

    pub fn set_secondary_head(&mut self, head: Option<usize>) -> Option<usize> {
        mem::replace(&mut self.secondary_head, head)
    }

    pub fn set_secondary_edge<S>(&mut self, pos: Option<S>) -> Option<String>
    where
        S: Into<String>,
    {
        mem::replace(&mut self.pos, pos.map(|i| i.into()))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Node {
    Root,
    Token(Token),
}

impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Node::Root => write!(f, "ROOT"),
            Node::Token(token) => write!(f, "{}", token.form()),
        }
    }
}

impl DepGraph<Projective> {
    pub fn try_from_dep_graph(graph: DepGraph<NonProjective>) -> Result<Self, String> {
        match flip_edges(graph.into_inner()) {
            Ok(graph) => Ok(DepGraph(graph, PhantomData)),
            Err(err) => Err(err),
        }
    }
}

fn flip_edges(mut graph: DiGraph<Node, String>) -> Result<DiGraph<Node, String>, String> {
    for idx in graph.node_indices().skip(1) {
        let edge = graph.first_edge(idx, Direction::Incoming).unwrap();
        let (head, _) = graph.edge_endpoints(edge).unwrap();
        let label = graph.remove_edge(edge);
        let (new_head, new_label) = if let Node::Token(ref mut token) = &mut graph[idx] {
            let new_head = token.set_secondary_head(Some(head.index()));
            let new_label = token.set_secondary_edge(label);
            match (new_head, new_label) {
                (Some(head), Some(label)) => (head, label),
                (_, _) => return Err("No secondary edges".to_string()),
            }
        } else {
            continue;
        };
        graph.add_edge(node_index(new_head), idx, new_label);
    }

    Ok(graph)
}

pub struct NonProjective{}
pub struct Projective{}

pub struct DepGraph<Type = NonProjective>(DiGraph<Node, String>, PhantomData<Type>);

impl Default for DepGraph {
    fn default() -> Self {
        let mut g = DiGraph::new();
        g.add_node(Node::Root);
        DepGraph(g, PhantomData)
    }
}

impl DepGraph<NonProjective> {
    pub fn try_from_p_dep_graph(pgraph: DepGraph<Projective>) -> Result<Self, String> {
        match flip_edges(pgraph.into_inner()) {
            Ok(graph) => Ok(DepGraph(graph, PhantomData)),
            Err(err) => Err(err),
        }
    }
}

impl<Type> DepGraph<Type> {
    pub(crate) fn new(graph: DiGraph<Node, String>) -> Self {
        DepGraph(graph, PhantomData)
    }

    pub fn push_token(&mut self, token: Token) {
        self.0.add_node(Node::Token(token));
    }

    /// Add a dependency relation between `head` and `dependent`.
    ///
    /// If `dependent` already has a head relation, this relation is removed
    /// to ensure single-headedness.
    pub fn add_relation(&mut self, head: usize, dependent: usize, deprel: String) {
        // Remove existing head relation (when present).
        if let Some(idx) = self
            .0
            .first_edge(node_index(dependent), Direction::Incoming)
        {
            self.0.remove_edge(idx);
        }

        self.0
            .add_edge(node_index(head), node_index(dependent), deprel);
    }

    pub fn inner(&self) -> &DiGraph<Node, String> {
        &self.0
    }

    pub fn into_inner(self) -> DiGraph<Node, String> {
        self.0
    }

    pub fn from_graph_indices(
        mut graph: DiGraph<Node, String>,
        indices: Vec<NodeIndex>,
    ) -> Result<Self, DepGraphError> {
        let mut ret_graph = Graph::with_capacity(graph.node_count(), graph.edge_count());
        let mut old_to_new_indices = vec![0usize; graph.node_count()];
        for (sent_idx, old_idx) in indices.into_iter().enumerate() {
            ret_graph.add_node(mem::replace(&mut graph[old_idx], Node::Root));
            old_to_new_indices[old_idx.index()] = sent_idx;
        }

        let (_, edges) = graph.into_nodes_edges();
        let mut has_head = vec![false; ret_graph.node_count()];

        for edge in edges.into_iter() {
            if has_head[edge.target().index()] {
                return Err(DepGraphError::MultiheadedToken {
                    value: "Multiheaded token".to_string(),
                });
            }
            has_head[edge.target().index()] = true;
            ret_graph.add_edge(edge.source(), edge.target(), edge.weight);
        }

        if is_cyclic_directed(&ret_graph) {
            return Err(DepGraphError::CyclicGraph {
                value: "Graph contains cycle".to_string(),
            });
        };

        Ok(DepGraph(ret_graph, PhantomData))
    }

    pub fn from_graph(graph: DiGraph<Node, String>) -> Result<Self, DepGraphError> {
        if is_cyclic_directed(&graph) {
            return Err(DepGraphError::CyclicGraph {
                value: "Graph contains cycle".to_string(),
            });
        };

        let mut has_head = vec![false; graph.node_count()];

        for edge in graph.edge_references() {
            if has_head[edge.target().index()] {
                return Err(DepGraphError::MultiheadedToken {
                    value: "Multiheaded token".to_string(),
                });
            }
            has_head[edge.target().index()] = true;
        }
        Ok(DepGraph(graph, PhantomData))
    }
}

impl<Type> Index<usize> for DepGraph<Type> {
    type Output = Node;

    fn index(&self, idx: usize) -> &Self::Output {
        &self.0[node_index(idx)]
    }
}

pub enum DepRel {
    /// Projective dependency relation
    PREL(String),
    /// Non-projective dependency relation
    REL(String),
}
#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use petgraph::dot::Dot;
    use ReadSentence;
    use Reader;
    use graph::DepGraph;

    static DEP: &[u8; 55] = b"1	Er	a	_	_	_	2	SUBJ	0	ROOT\n\
2	geht	b	_	_	_	0	ROOT	1	SUBJ";

    #[test]
    fn secondary_edges() {
        let c = Cursor::new(DEP.to_vec());
        let mut reader = Reader::new(c);

        let og = reader.read_sentence_to_graph().unwrap().unwrap();
        println!("{}", Dot::new(og.inner()));
        let pg = DepGraph::try_from_dep_graph(og).unwrap();
        let g = pg.into_inner();
        println!("{}", Dot::new(&g));
    }
}
