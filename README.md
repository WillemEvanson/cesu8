# CESU-8 Encoder & Decoder

Converts between normal UTF-8 and CESU-8 encodings.

CESU-8 encodes characters outside the Basic Multilingual Plane as two UTF-16
surrogate characters, which are then re-encoded as 3-byte UTF-8 characters.
This means that 4-byte UTF-8 sequences become 6-byte CESU-8 sequences.

We also support Java's Modified UTF-8 encoding, which uses a variant of CESU-8
encoding `\0` using a two-byte sequence.