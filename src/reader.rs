use std::io;

use failure::Error;

use error::ReadError;
use features::Features;
use token::EMPTY_TOKEN;
use {DepTriple, Sentence, Token};

/// A trait for objects that can read CoNLL-X `Sentence`s
pub trait ReadSentence {
    /// Read a `Sentence` from this object.
    ///
    /// # Errors
    ///
    /// A call to `read_sentence` may generate an error to indicate that
    /// the operation could not be completed.
    fn read_sentence(&mut self) -> Result<Option<Sentence>, Error>;

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
    type Item = Result<Sentence, Error>;
    type IntoIter = Sentences<Reader<R>>;

    fn into_iter(self) -> Self::IntoIter {
        self.sentences()
    }
}

impl<R: io::BufRead> ReadSentence for Reader<R> {
    fn read_sentence(&mut self) -> Result<Option<Sentence>, Error> {
        let mut line = String::new();
        let mut sentence = Sentence::new();
        let mut edges = Vec::new();
        let mut proj_edges = Vec::new();

        loop {
            line.clear();

            // End of reader.
            if self.read.read_line(&mut line)? == 0 {
                if sentence.len() == 1 {
                    return Ok(None);
                }

                add_edges(&mut sentence, edges, proj_edges);

                return Ok(Some(sentence));
            }

            // The blank line is a sentence separator. We want to be robust
            // in the case a CoNLL file is malformed and has two newlines as
            // a separator.
            if line.trim().is_empty() {
                if sentence.len() == 1 {
                    continue;
                }

                add_edges(&mut sentence, edges, proj_edges);

                return Ok(Some(sentence));
            }

            let mut iter = line.trim().split_terminator('\t');

            parse_identifier_field(iter.next())?;

            let mut token = Token::new(parse_form_field(iter.next())?);
            token.set_lemma(parse_string_field(iter.next()));
            token.set_cpos(parse_string_field(iter.next()));
            token.set_pos(parse_string_field(iter.next()));
            token.set_features(parse_string_field(iter.next()).map(Features::from_string));

            // Head relation.
            if let Some(head) = parse_numeric_field(iter.next())? {
                let head_rel = parse_string_field(iter.next());
                edges.push(DepTriple::new(head, head_rel, sentence.len()));
            }

            // Projective head relation.
            if let Some(proj_head) = parse_numeric_field(iter.next())? {
                let proj_head_rel = parse_string_field(iter.next());
                proj_edges.push(DepTriple::new(proj_head, proj_head_rel, sentence.len()));
            }

            //token.set_head();
            //token.set_head_rel();
            //token.set_p_head(parse_numeric_field(iter.next())?);
            //token.set_p_head_rel(parse_string_field(iter.next()));

            sentence.push(token);
        }
    }
}

fn add_edges(
    sentence: &mut Sentence,
    edges: Vec<DepTriple<String>>,
    proj_edges: Vec<DepTriple<String>>,
) {
    for edge in edges {
        sentence.dep_graph_mut().add_deprel(edge);
    }

    for edge in proj_edges {
        sentence.proj_dep_graph_mut().add_deprel(edge);
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
    type Item = Result<Sentence, Error>;

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

    use tests::{read_sentences, TEST_SENTENCES};
    use {ReadSentence, Sentence};

    static BASIC: &str = "testdata/basic.conll";

    static DOUBLE_NEWLINE: &str = "testdata/double-newline.conll";

    static EMPTY: &str = "testdata/empty.conll";

    fn string_reader(s: &str) -> Box<BufRead> {
        Box::new(Cursor::new(s.as_bytes().to_owned()))
    }

    fn test_parsing(correct: &[Sentence], fragment: &str) {
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
