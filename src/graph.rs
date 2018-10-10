use std::mem;
use std::ops::Index;

use petgraph::graph::{node_index, DiGraph};
use petgraph::Direction;

use Features;

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
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Node {
    Root,
    Token(Token),
}

pub struct DepGraph(DiGraph<Node, String>);

impl Default for DepGraph {
    fn default() -> Self {
        let mut g = DiGraph::new();
        g.add_node(Node::Root);
        DepGraph(g)
    }
}

impl DepGraph {
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
}

impl Index<usize> for DepGraph {
    type Output = Node;

    fn index(&self, idx: usize) -> &Self::Output {
        &self.0[node_index(idx)]
    }
}
