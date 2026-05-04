
function calculateTotal(product, quantity) {
  return product.price * quantity;
}

var item = {
  name: "Wireless Mouse",
  cost: 25 // Note the property name is 'cost', not 'price'
};

console.log(calculateTotal(item, 2));
