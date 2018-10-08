use std::io;

use failure::Error;
use petgraph::graph::{DiGraph, node_index};

use features::Features;
use token::{DependencyGraph, SimpleToken, EMPTY_TOKEN, DepRel};
use error::ReadError;


/// A trait for objects that can read CoNLL-X `Sentence`s
pub trait ReadSentence {
    /// Read a `Sentence` from this object.
    ///
    /// # Errors
    ///
    /// A call to `read_sentence` may generate an error to indicate that
    /// the operation could not be completed.
    fn read_sentence(&mut self) -> Result<Option<DependencyGraph>, Error>;

    /// Get an iterator over the sentences in this reader.
    fn sentences(self) -> Sentences<Self>
    where
        Self: Sized,
    {
        Sentences { reader: self }
    }
}

/// A reader for CoNLL-X sentences.
pub struct Reader<R> {
    read: R,
}

impl<R: io::BufRead> Reader<R> {
    /// Construct a new reader from an object that implements the
    /// `io::BufRead` trait.
    pub fn new(read: R) -> Reader<R> {
        Reader { read: read }
    }
}

impl<R: io::BufRead> IntoIterator for Reader<R> {
    type Item = Result<DependencyGraph, Error>;
    type IntoIter = Sentences<Reader<R>>;

    fn into_iter(self) -> Self::IntoIter {
        self.sentences()
    }
}

impl<R: io::BufRead> ReadSentence for Reader<R> {
    fn read_sentence(&mut self) -> Result<Option<DependencyGraph>, Error> {
        let mut line = String::new();

        let mut graph = DiGraph::new();
        graph.add_node(SimpleToken::Root);
        let mut edges = Vec::new();

        loop {
            line.clear();

            // End of reader.
            if self.read.read_line(&mut line)? == 0 {
                if graph.node_count() == 1 {
                    return Ok(None);
                }

                add_edges(&mut graph, edges);

                return Ok(Some(graph));
            }

            // The blank line is a sentence separator. We want to be robust
            // in the case a CoNLL file is malformed and has two newlines as
            // a separator.
            if line.trim().is_empty() {
                if graph.node_count() == 1 {
                    continue;
                }

                add_edges(&mut graph, edges);

                return Ok(Some(graph));
            }

            let mut iter = line.trim().split_terminator('\t');

            parse_identifier_field(iter.next())?;

            let form = parse_form_field(iter.next())?;
            let lemma = parse_string_field(iter.next());
            let cpos = parse_string_field(iter.next());
            let pos = parse_string_field(iter.next());
            let features = parse_string_field(iter.next()).map(Features::from_string);

            graph.add_node(SimpleToken::Token {
                form,
                lemma,
                cpos,
                pos,
                features,
            });

            let head = parse_numeric_field(iter.next())?;
            let head_rel = parse_string_field(iter.next());
            if let (Some(head), Some(head_rel)) = (head, head_rel) {
              edges.push((head, graph.node_count(), DepRel::NonProjective(head_rel)));
            }

            let head = parse_numeric_field(iter.next())?;
            let head_rel = parse_string_field(iter.next());
            if let (Some(head), Some(head_rel)) = (head, head_rel) {
              edges.push((head, graph.node_count(), DepRel::Projective(head_rel)));
            }
        }
    }
}



fn add_edges(graph: &mut DependencyGraph, edges: Vec<(usize, usize, DepRel)>) {
    for (head, dep, rel) in edges {
        graph.add_edge(node_index(head), node_index(dep), rel);
    }
}

/// An iterator over the sentences in a `Reader`.
pub struct Sentences<R>
where
    R: ReadSentence,
{
    reader: R,
}

impl<R> Iterator for Sentences<R>
where
    R: ReadSentence,
{
    type Item = Result<DependencyGraph, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.reader.read_sentence() {
            Ok(None) => None,
            Ok(Some(sent)) => Some(Ok(sent)),
            Err(e) => Some(Err(e)),
        }
    }
}

fn parse_form_field(field: Option<&str>) -> Result<String, ReadError> {
    field.map(str::to_owned).ok_or(ReadError::MissingFormField)
}

fn parse_string_field(field: Option<&str>) -> Option<String> {
    field.and_then(|s| {
        if s == EMPTY_TOKEN {
            None
        } else {
            Some(s.to_string())
        }
    })
}

fn parse_identifier_field(field: Option<&str>) -> Result<Option<usize>, ReadError> {
    match field {
        None => {
            return Err(ReadError::ParseIdentifierField {
                value: "A token identifier should be present".to_owned(),
            }.into())
        }
        Some(s) => {
            if s == EMPTY_TOKEN {
                return Err(ReadError::ParseIdentifierField {
                    value: s.to_owned(),
                }.into());
            }

            Ok(Some(s.parse::<usize>().map_err(|_| {
                ReadError::ParseIntField {
                    value: s.to_owned(),
                }
            })?))
        }
    }
}

fn parse_numeric_field(field: Option<&str>) -> Result<Option<usize>, ReadError> {
    match field {
        None => Ok(None),
        Some(s) => if s == EMPTY_TOKEN {
            Ok(None)
        } else {
            Ok(Some(s.parse::<usize>().map_err(|_| {
                ReadError::ParseIntField {
                    value: s.to_owned(),
                }
            })?))
        },
    }
}

#[cfg(test)]
mod tests {

    use std::io::{BufRead, Cursor};

    use {ReadSentence, Token};
    use tests::{read_sentences, TEST_SENTENCES};

    static BASIC: &str = "testdata/basic.conll";

    static DOUBLE_NEWLINE: &str = "testdata/double-newline.conll";

    static EMPTY: &str = "testdata/empty.conll";

    fn string_reader(s: &str) -> Box<BufRead> {
        Box::new(Cursor::new(s.as_bytes().to_owned()))
    }

    fn test_parsing(correct: &[Vec<Token>], fragment: &str) {
        let sentences = read_sentences(fragment);
        assert_eq!(correct.as_ref(), sentences.as_slice());
    }

    #[test]
    fn reader() {
        test_parsing(&*TEST_SENTENCES, BASIC);
    }

    #[test]
    fn reader_robust() {
        test_parsing(&*TEST_SENTENCES, DOUBLE_NEWLINE);
    }

    #[test]
    fn reader_marked_empty() {
        test_parsing(&*TEST_SENTENCES, EMPTY);
    }

    #[test]
    #[should_panic(expected = "ParseIntField")]
    fn reader_rejects_non_numeric_id() {
        let mut reader = super::Reader::new(string_reader("test"));
        reader.read_sentence().unwrap();
    }

    #[test]
    #[should_panic(expected = "ParseIdentifierField")]
    fn reader_rejects_underscore_id() {
        let mut reader = super::Reader::new(string_reader("_"));
        reader.read_sentence().unwrap();
    }

}
