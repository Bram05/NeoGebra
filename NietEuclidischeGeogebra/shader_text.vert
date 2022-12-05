#version 420 core

layout(location =0) in vec4 vertex;

out vec2 texture_coordinates;

void main(void)
{
texture_coordinates = vec2(vertex[2],vertex[3]);
gl_Position = vec4(vertex.xy,0.0,1.0);
}