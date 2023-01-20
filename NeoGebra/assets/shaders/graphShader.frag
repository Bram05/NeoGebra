#version 430 core

out vec4 colour;
in vec2 TexCoords;

uniform vec4 u_Colour;
uniform sampler2D tex;

uniform int u_Size;
	
void main()
{   
    float biggest = 0.0;
    // Maybe change this to be all points within a distance u_Size from this centre instead
    for (int x = 0; x < u_Size; x++) {
        for (int y = 0; y < u_Size; y++) {
            // TODO: line thickness uitproberen
            vec2 coord = TexCoords + vec2(x - int(u_Size/2), y - int(u_Size/2) ) / vec2(textureSize(tex,0));
            if (!isnan(biggest))
                biggest = max(biggest, texture(tex, coord).r);
        }
    }
    colour = vec4(u_Colour.xyz, biggest);
}