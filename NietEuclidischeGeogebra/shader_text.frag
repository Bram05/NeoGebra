#version 420 core


in vec2 texture_coordinates;
out vec4 fragment_colour;

uniform vec3 font_colour;
uniform sampler2D alphabet_texture;


void main(void)
{
fragment_colour = vec4(font_colour/255, texture(alphabet_texture,texture_coordinates).r);
}