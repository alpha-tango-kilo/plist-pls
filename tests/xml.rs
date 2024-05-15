use plist_pls::{print_miette, xml::XmlDocument};

// TODO: snapshot testing, or do I actually want to write out the full struct?
#[test]
fn whole_doc() {
    let source = include_str!("../test_data/xml.plist");
    let doc = match XmlDocument::from_str(source) {
        Ok(doc) => doc,
        Err(why) => {
            print_miette(&why);
            panic!("should load document");
        },
    };
    eprintln!("{doc:#?}");
}
