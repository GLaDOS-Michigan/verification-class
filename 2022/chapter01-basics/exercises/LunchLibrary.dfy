//#desc Library for exercises 13 & 14

// This whole product-sum idea gets clearer when we use both powers
// (struct/product, union/sum) at the same time.

datatype Meat = Salami | Ham
datatype Cheese = Provolone | Swiss | Cheddar | Jack
datatype Veggie = Olive | Onion | Pepper
datatype Order =
    Sandwich(meat:Meat, cheese:Cheese)
  | Pizza(meat:Meat, veggie:Veggie)
  | Appetizer(cheese:Cheese)

// There are 2 Meats, 4 Cheeses, and 3 Veggies.
// Thus there are 8 Sandwiches, 6 Pizzas, and 4 Appetizers.
// Thus there are 8+6+4 = 18 Orders.
// This is why they're called "algebraic" datatypes.
