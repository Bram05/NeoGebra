# NeoGebra

NeoGebra is a program that can be used for creating and verifying Non-Euclidean models.

## Screenshots

  <img src="https://raw.githubusercontent.com/Bram05/NeoGebra/main/NeoGebra/assets/images/Example1.png" width=30% />
  <img src="https://raw.githubusercontent.com/Bram05/NeoGebra/main/NeoGebra/assets/images/Example2.png" width=30% /> 
  <img src="https://raw.githubusercontent.com/Bram05/NeoGebra/main/NeoGebra/assets/images/Example3.png" width=30% />

## Features

- Sample Non-Euclidean models built-in, such as the Poincare model, Beltrami-Klein model and the half plane model.
- Custom Non-Euclidean models, with your own identifiers
- Postulates verifier
- Cross-platform

## Table of content

- [NeoGebra](#neogebra)
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
    - [Variables](#variables)
  - [Run Locally](#run-locally)
  - [Creators](#creators)

## Usage

### Model

First of all, you will have to choose a model that you would like to work in. The model could be either chosen with the menu on the top, or by creating your own model. If you would like to know more about creating models, refer to [this section](##Custom-models).

### Points

A point is a definition which doesn't certainly have the same definition in different models. The 3 built-in models have however the same point identifiers, p0 and p1. The way you can create a point is by filling in the identifiers. This can be done by separating each identifier by a comma ( , ).
For example valid points in the Poincare model would be:

> 0.5,0.51 <br>
> 0.1,-0.2 <br>

For decimals you should use a point ( . )

### Lines

Just like a point, a line isn't universally defined. Each model has it's own definition, for example the Poincare model and the half-plane model have 2 identifiers, while the Beltrami-Klein model has 3. Again, identifiers are separated by a comma ( , )

Beltrami-Klein model line examples:

> 0,1,0.7 <br>
> 0.3,0.1,-0.1 <br>

For decimals you should use a point ( . )

### Construct line from 2 points

If you would like to construct a line from 2 points, you will first have to [create 2 points](###points).<br>
Once you create the 2 points, you can create a line by using the index of the points. Let's say you have points:

> 1: 0.1,0.1 <br>
> 2: -0.1,0.3 <br>

You can create a line in this way:

> 1,2

This will draw a line on the graph through both points.

### Get point of intersection from 2 lines

If you would like to get the point of intersection from 2 lines, you will first have to [create 2 lines](###lines).<br>
Once you create the 2 lines, you can get the point by using the index of the lines. Let's say you have lines:

> 1: 0.1,0.1 <br>
> 2: -0.1,0.3 <br>

You can get the point in this way:

> 1,2

This will draw the point of intersection of both lines.

## Custom models

In NeoGebra you have the ability to create your own models. This can be done by filling in the:

### Point definition

What does a point mean in your model? Is it a euclidean point or do you have to convert it? Is your model infinite in the sense of euclidean geometry when you display it on a plane? Or are it's boundaries the unit circle like the Poincare model or the Beltrami-Klein model?

A point could be identified by 1 or more identifiers and has it's boundaries set. For example all points within the unit circle could be defined as:

> x = p0 & y = p1 & x^2 + y^2 < 1

This basically means that, the x coordinate is equal to p0 (first point identifier), and the y coordinate is equal to p1. AND that the point is within the circle with radius 1.

### Lines definition

how the line looks, boundaries

### Incidence definition

what does incidence with a point and a line mean

### Betweennes definition

how is points betweennes defined? what does point b between a and c mean

### Congruence definition

distance?

### Line from 2 points definition

how to create a line from 2 points?

### Intersection of 2 lines definition

how to get the value of 2 lines with a point

### Variables

extra variables to be used in your definitions????

## Run Locally

clone, run, vs todo

## Creators

This program is built for a school project and made by:

- [JoenPoenMan](https://github.com/JoenPoenMan)
- [RiadZX](https://github.com/RiadZX)
- [Bram05](https://github.com/Bram05)
