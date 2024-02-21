// use crate::*;

// use turtle_graphics::{Canvas, Turtle};
use lambdas::{Canvas, Turtle};
use ordered_float::OrderedFloat;

fn main() {
    let mut t = Canvas::new();
    // move the turtle 100.0 points upwards
    t.forward(OrderedFloat(50.0));
    // rotate the head of the turtle by 90 degree to the right
    t.right(OrderedFloat(90.0));
    // move 100.0 forward again (now to the right).
    t.forward(OrderedFloat(50.0));

    for _ in 0..360 {
        // Move forward three steps
        t.forward(OrderedFloat(1.0));
        // Rotate to the right (clockwise) by 1 degree
        t.right(OrderedFloat(5.0));
    }
    // ...

    // write the graphic (SVG) to stdout.
    t.save_svg(&mut std::io::stdout()).unwrap();

    // or write it as EPS
    // t.save_eps(&mut File::create("test.eps").unwrap()).unwrap();
}
