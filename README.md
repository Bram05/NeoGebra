# NeoGebra 💫

NeoGebra is a program that can be used for creating, visualizing and verifying Non-Euclidean models.

## Screenshots

  <img src="https://raw.githubusercontent.com/Bram05/NeoGebra/main/NeoGebra/assets/images/Example1.png" width=auto />
  <img src="https://raw.githubusercontent.com/Bram05/NeoGebra/main/NeoGebra/assets/images/Example2.png" width=auto /> 
  <img src="https://raw.githubusercontent.com/Bram05/NeoGebra/main/NeoGebra/assets/images/Example3.png" width=auto />

## Features

- Sample Non-Euclidean models built-in, such as the Poincare model, Beltrami-Klein model and the half plane model.
- Compare models
- Custom Non-Euclidean models, with your own identifiers
- Postulates verifier
- Cross-platform (MacOS untested)

## Table of content

- [NeoGebra 💫](#neogebra-)
  - [Screenshots](#screenshots)
  - [Features](#features)
  - [Table of content](#table-of-content)
  - [Usage](#usage)
    - [Model](#model)
    - [Points](#points)
    - [Lines](#lines)
    - [Construct line from 2 points](#construct-line-from-2-points)
    - [Get point of intersection from 2 lines](#get-point-of-intersection-from-2-lines)
  - [Custom models](#custom-models)
    - [Point definition](#point-definition)
    - [Lines definition](#lines-definition)
    - [Incidence definition](#incidence-definition)
    - [Betweennes definition](#betweennes-definition)
    - [Congruence definition](#congruence-definition)
    - [Line from 2 points definition](#line-from-2-points-definition)
    - [Intersection of 2 lines definition](#intersection-of-2-lines-definition)
    - [Extras](#extras)
      - [Variables](#variables)
      - [Equations](#equations)
  - [Build \& run from source](#build--run-from-source)
    - [Prerequisites](#prerequisites)
  - [Creators](#creators)

## Usage

### Model

First of all, you will have to choose a model that you would like to work in. The model could be either chosen with the menu on the top, or by creating your own model. If you would like to know more about creating models, refer to [this section](#Custom-models).

### Points

A point is a definition which doesn't certainly have the same definition in different models. The 3 built-in models have however the same point identifiers, p0 and p1. The way you can create a point is by filling in the identifiers. This can be done by separating each identifier by a comma ( , ).
For example valid points in the Poincare model would be:

> 0.5,0.51 <br>
> 0.1,-0.2

For decimals you should use a point ( . )

### Lines

Just like a point, a line isn't universally defined. Each model has it's own definition, for example the Poincare model and the half-plane model have 2 identifiers, while the Beltrami-Klein model has 3. Again, identifiers are separated by a comma ( , )

Beltrami-Klein model line examples:

> 0,1,0.7 <br>
> 0.3,0.1,-0.1 <br>

For decimals you should use a point ( . )

### Construct line from 2 points

If you would like to construct a line from 2 points, you will first have to [create 2 points](#Points).<br>
Once you create the 2 points, you can create a line by using the index of the points. Let's say you have points:

> 1️⃣: 0.1,0.1 <br>
> 2️⃣: -0.1,0.3

You can create a line in this way:

> 1,2

This will draw a line on the graph through both points.

### Get point of intersection from 2 lines

If you would like to get the point of intersection from 2 lines, you will first have to [create 2 lines](#lines).<br>
Once you create the 2 lines, you can get the point by using the index of the lines. Let's say you have lines:

> 1️⃣: 0.1,0.1 <br>
> 2️⃣: -0.1,0.3

You can get the point in this way:

> 1,2

This will draw the point of intersection of both lines.

## Custom models

In NeoGebra you have the ability to create your own models. This can be done by filling in the following points.

### Point definition

What does a point mean in your model? Is it a euclidean point or do you have to convert it? Is your model infinite in the sense of euclidean geometry when you display it on a plane? Or are it's boundaries the unit circle like the Poincare model or the Beltrami-Klein model?

A point could be identified by 1 or more identifiers and has it's boundaries set. For example all points within the unit circle could be defined as:

> x = p0 & y = p1 & x^2 + y^2 < 1

This basically means that, the x coordinate is equal to p0 (first point identifier), and the y coordinate is equal to p1. AND that the point is within the circle with radius 1.

### Lines definition

What's the formula of a line in your model? It could be a straight euclidean line , or an arc of a circle of whose center is outside the unit circle for example. You will have to define the formula of a line using as many identifiers as you wish. A Euclidean line is usually defined as y = ax + b or ax + by = c. <br>This could be translated to:
| y = ax + b | ax + by = c |
|-------------|----------------------|
| y = l0 \* x + l1 | l0 \* x + l1 \* y = l2 |
|l0,l1|l0,l1,l2|

With the first example, we have 2 line identifiers, however with the second one we require 3 identifiers.

### Incidence definition

You will also have to define the definition of intersection between a point and a line. When is point p considered to be on line l? We will continue with the same example given in the [line definition section](#lines-definition). Take definition of line l :

> l0\*x+l1\*y=l2 & x^2 + y^2 < 1

And point definition:

> x = p0 & y = p1 & x^2 + y^2 < 1

In this case, filling in point p in the line definition is sufficient to check if it's valid.

> p0\*l0+l1\*p1=1

So this will be your incidence definition.

### Betweennes definition

Here you will have to define a betweennes axiom in your model. Let's say you have points {p,q,r}. Then the definition will have to validate if q is between p and r, and if q is between r and p. For examples you can view the built-in models

### Congruence definition

Here you will have to define an equation to calculate the distance between 2 points. To make it clearer, to calculate distance between Euclidean points you use this formula:

> Point P (p0,p1), Point Q (q0,q1))

distance(P,Q) = $\sqrt{(q1-p1)^2 + (q0-p0)^2}$

### Line from 2 points definition

You can create a definition of creating a line using 2 points. Your input will be points and the output will be a line (if possible) drawn on the graph. For examples you can view the built-in models

### Intersection of 2 lines definition

how to get the value of 2 lines with a point
You can create a definition of 2 intersecting lines. As an input you will use 2 created lines and as an output a point will be drawn (if possible) on the graph at the intersection point. For examples you can view the built-in models

### Extras

#### Variables

The main goal of variables is to make definitions more readable and easier for you. You can define variables in the variable menu. To access the variable menu, you click on the button vairables next to the field of the definition. A variable menu will pop-up where you can specify the name the variable on the left-side, and it's value on the right-side.

> ✅ You can use point identifiers in the definition , such as p0,p1,q0,q1 <br>
> ❌ You can not use x or y in the definition

Let's say you created a point variable `r`, to access it in the definition of a point you simply use : `p.r`. <br>
If you created a line variable `n`, you can access it similarly with `l.n`

#### Equations

Just like extra variables you can add in extra lines to help you visualize your models. For example in the Poincare or Beltrami-Klein models you can add a unit circle to help you visualize it.

## Build & run from source

### Prerequisites

- [Visual Studio 2022](https://visualstudio.microsoft.com/vs/)
- [CMake C++ Compiler](https://cmake.org/)
- [Git](https://git-scm.com/)

1. Clone the repository using the following command

```bash
git clone https://github.com/Bram05/NeoGebra.git --recursive
```

2. Open the project in [Visual Studio 2022](https://visualstudio.microsoft.com/vs/).
3. Run the program with `F5`.

## Creators

This program is built for a school project and made by:

- [JoenPoenMan](https://github.com/JoenPoenMan)
- [RiadZX](https://github.com/RiadZX)
- [Bram05](https://github.com/Bram05)
