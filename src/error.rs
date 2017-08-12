error_chain!{
    foreign_links {
        Io(::std::io::Error);
    }

    errors {
        MissingFormFieldError {
            description("form field is missing")
            display("form field is missing")
        }

        ParseIntFieldError(value: String) {
            description("cannot parse integer field")
            display("cannot parse as integer field: '{}'", value)
        }

        ParseIdentifierFieldError(value: String) {
            description("cannot parse identifier field")
            display("cannot parse as identifier field: '{}'", value)
        }

        IncompleteGraphError(value: String) {
            description("incomplete graph")
            display("incomplete graph: '{}'", value)
        }
    }
}
